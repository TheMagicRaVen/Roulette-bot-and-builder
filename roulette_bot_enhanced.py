import pyautogui
import json
import time
import os
import pytesseract
import glob
import random
import copy
import threading
try:
    import keyboard
    KEYBOARD_AVAILABLE = True
    KEYBOARD_METHOD = 'keyboard'
except ImportError:
    KEYBOARD_AVAILABLE = False
    KEYBOARD_METHOD = None
    print("[!] WARNING: keyboard module not installed. Trying alternative...")
    
    # Try pynput as fallback
    try:
        from pynput import keyboard
        KEYBOARD_AVAILABLE = True
        KEYBOARD_METHOD = 'pynput'
        print("[!] Using pynput for ESC key monitoring")
    except ImportError:
        print("[!] WARNING: No keyboard library available. Using tkinter fallback.")
        KEYBOARD_AVAILABLE = True
        KEYBOARD_METHOD = 'tkinter'
        print("[!] Using tkinter for ESC key monitoring (GUI must be focused)")
        print("[!] For better ESC key support, install: pip install keyboard")
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs
from PIL import Image
from pyclick import HumanClicker
import tkinter as tk
from tkinter import ttk
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import matplotlib.ticker as ticker
import numpy as np

# --- CONFIGURATIE ---
pytesseract.pytesseract.tesseract_cmd = r'C:\Program Files\Tesseract-OCR\tesseract.exe'
HISTORY_REGION = (602, 1, 46, 41) 

class RouletteBot:
    def __init__(self):
        pyautogui.FAILSAFE = True
        self.hc = HumanClicker()
        self.coords = self.load_json('config_coords.json')
        self.tafel_marker = 'assets/ui/tafel_marker.png'
        self.download_path = os.path.join(os.path.expanduser('~'), 'Downloads')
        self.current_strategy_file = None
        self.strategy_trackers = []
        self.first_run_done = False
        self.knop_was_weg = False 
        self.all_strategies = []  # Store all loaded strategies for switching
        
        # Rebet system
        self.last_bet_totals = {}  # Store last bet amounts
        self.can_use_rebet = False  # Track if rebet is available
        
        # OCR results for HTML tool
        self.ocr_results = []  # Store recent OCR results
        self.http_server = None
        self.server_thread = None
        self.last_spin_result = None  # Track the final result of completed spin
        self.spin_in_progress = False  # Track if spin is currently in progress
        self.strategy_switched_this_round = False  # Prevent multiple switches per round
        
        # GUI and visualization
        self.gui_root = None
        self.profit_loss_window = None
        self.strategies_window = None
        self.profit_history = []  # Track profit/loss over time
        self.round_history = []  # Track round numbers
        self.total_profit = 0  # Current total profit/loss
        self.round_count = 0  # Current round number
        
        # Bot control
        self.stop_bot = False  # Flag to stop bot when ESC is pressed
        
        # Start ESC key monitoring if available
        if KEYBOARD_AVAILABLE:
            self.start_esc_monitor()
        
    def start_esc_monitor(self):
        """Start monitoring Ctrl+ESC key combination to stop the bot"""
        if not KEYBOARD_AVAILABLE:
            return
            
        def on_ctrl_esc_press():
            self.stop_bot = True
            print("\n[!] Ctrl+ESC pressed - Stopping bot...")
            # Stop all strategies
            for strategy in self.strategy_trackers:
                strategy['is_stopped'] = True
                strategy['is_active'] = False
            print("[!] All strategies stopped")
        
        # Register Ctrl+ESC handler based on available library
        if KEYBOARD_METHOD == 'keyboard':
            # Simple approach: check for Ctrl+ESC combination
            def check_ctrl_esc():
                try:
                    ctrl_pressed = keyboard.is_pressed('ctrl')
                    esc_pressed = keyboard.is_pressed('esc')
                    if ctrl_pressed and esc_pressed:
                        print("[!] Ctrl+ESC detected!")
                        on_ctrl_esc_press()
                        return True
                except Exception as e:
                    print(f"[!] Key check error: {e}")
                return False
            
            def monitor_keys():
                while not self.stop_bot:
                    if check_ctrl_esc():
                        break
                    time.sleep(0.1)  # Check every 100ms
            
            # Test keyboard library
            try:
                test_result = keyboard.is_pressed('shift')
                print(f"[!] Keyboard library test: {'Working' if test_result is not None else 'Failed'}")
            except Exception as e:
                print(f"[!] Keyboard library test failed: {e}")
            
            # Start monitoring in a separate thread
            import threading
            monitor_thread = threading.Thread(target=monitor_keys, daemon=True)
            monitor_thread.start()
            print("[!] Ctrl+ESC key monitoring enabled (keyboard) - Press Ctrl+ESC to stop the bot")
        elif KEYBOARD_METHOD == 'pynput':
            # Use pynput listener for Ctrl+ESC
            def on_press(key):
                try:
                    # Check if Ctrl is pressed with ESC
                    if key == keyboard.Key.esc and keyboard.Key.ctrl in self._pressed_keys:
                        on_ctrl_esc_press()
                        return False  # Stop listener
                    elif key == keyboard.Key.ctrl:
                        self._pressed_keys.add(keyboard.Key.ctrl)
                    elif key == keyboard.Key.esc:
                        return  # Ignore ESC without Ctrl
                except AttributeError:
                    if key == 'esc' and 'ctrl' in self._pressed_keys:
                        on_ctrl_esc_press()
                        return False  # Stop listener
                    elif key == 'ctrl':
                        self._pressed_keys.add('ctrl')
                    elif key == 'esc':
                        return  # Ignore ESC without Ctrl
            
            def on_release(key):
                try:
                    if key == keyboard.Key.ctrl:
                        self._pressed_keys.discard(keyboard.Key.ctrl)
                except AttributeError:
                    if key == 'ctrl':
                        self._pressed_keys.discard('ctrl')
            
            # Initialize pressed keys tracking
            self._pressed_keys = set()
            listener = keyboard.Listener(on_press=on_press, on_release=on_release)
            listener.daemon = True
            listener.start()
            print("[!] Ctrl+ESC key monitoring enabled (pynput) - Press Ctrl+ESC to stop the bot")
        elif KEYBOARD_METHOD == 'tkinter':
            # Use tkinter binding - will be set up when GUI is created
            print("[!] Ctrl+ESC key monitoring will be set up when GUI is created")
            self.esc_callback = on_ctrl_esc_press
        
    def add_ocr_result(self, number):
        """Add a new OCR result for the HTML tool and push to SSE connections ONLY when spin is complete"""
        import datetime
        result = {
            'number': number,
            'timestamp': datetime.datetime.now().isoformat(),
            'color': self.get_number_color(number)
        }
        
        # Check if this is a new result (different from last spin result)
        if self.last_spin_result != number:
            self.last_spin_result = number
            self.ocr_results.append(result)
            # Keep only last 50 results
            if len(self.ocr_results) > 50:
                self.ocr_results = self.ocr_results[-50:]
                
            # Only push update to SSE connections when we have a confirmed new result
            self.push_sse_update({'results': self.ocr_results})
        else:
            print(f"[!] OCR detected {number} but same as last result - ignoring")
        
    def get_number_color(self, number):
        """Get the color of a roulette number"""
        if number == 0:
            return 'green'
        red_numbers = [1, 3, 5, 7, 9, 12, 14, 16, 18, 19, 21, 23, 25, 27, 30, 32, 34, 36]
        return 'red' if number in red_numbers else 'black'
        
    def start_http_server(self):
        """Start HTTP server to serve OCR results to HTML tool"""
        class OCRRequestHandler(BaseHTTPRequestHandler):
            def __init__(self, bot, *args, **kwargs):
                self.bot = bot
                super().__init__(*args, **kwargs)
                
            def do_GET(self):
                if self.path == '/ocr-results':
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.send_header('Access-Control-Allow-Origin', '*')
                    self.end_headers()
                    response = json.dumps({'results': self.bot.ocr_results})
                    self.wfile.write(response.encode())
                elif self.path == '/ocr-stream':
                    self.send_response(200)
                    self.send_header('Content-type', 'text/event-stream')
                    self.send_header('Cache-Control', 'no-cache')
                    self.send_header('Access-Control-Allow-Origin', '*')
                    self.send_header('Connection', 'keep-alive')
                    self.end_headers()
                    
                    # Send initial results
                    initial_data = f"data: {json.dumps({'results': self.bot.ocr_results})}\n\n"
                    self.wfile.write(initial_data.encode())
                    
                    # Keep connection alive and send updates when new results arrive
                    self.bot.sse_connections.append(self)
                else:
                    self.send_error(404)
                    
            def log_message(self, format, *args):
                # Suppress server logs
                pass
        
        def handler(*args, **kwargs):
            OCRRequestHandler(self, *args, **kwargs)
            
        self.sse_connections = []  # Store SSE connections
        self.http_server = HTTPServer(('localhost', 8765), handler)
        self.server_thread = threading.Thread(target=self.http_server.serve_forever)
        self.server_thread.daemon = True
        self.server_thread.start()
        print("[!] HTTP server started on http://localhost:8765 for OCR results")
        
    def push_sse_update(self, data):
        """Push update to all SSE connections"""
        if hasattr(self, 'sse_connections'):
            message = f"data: {json.dumps(data)}\n\n"
            for connection in self.sse_connections[:]:  # Copy list to avoid modification during iteration
                try:
                    connection.wfile.write(message.encode())
                    connection.wfile.flush()
                except:
                    # Connection closed, remove it
                    self.sse_connections.remove(connection)

    def load_json(self, path):
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
    
    def create_gui_windows(self):
        """Create the GUI windows for visualization"""
        # Run GUI in separate thread to avoid blocking main bot
        gui_thread = threading.Thread(target=self._create_gui_windows_thread)
        gui_thread.daemon = True
        gui_thread.start()
        
    def _create_gui_windows_thread(self):
        """Create GUI windows in separate thread"""
        try:
            # Create main GUI root
            self.gui_root = tk.Tk()
            self.gui_root.title("Roulette Bot Analytics")
            self.gui_root.geometry("500x300")  # Original window size
            self.gui_root.configure(bg='#1a1a1a')
            
            # Make window always on top and add window state handling
            self.gui_root.attributes('-topmost', True)
            self.gui_root.protocol("WM_DELETE_WINDOW", self.on_window_close)  # Handle window close
            
            # Add Ctrl+ESC key binding if using tkinter method
            if KEYBOARD_METHOD == 'tkinter' and hasattr(self, 'esc_callback'):
                # Track Ctrl key state for tkinter
                self._ctrl_pressed = False
                
                def on_key_press(event):
                    if event.keysym == 'Control_L' or event.keysym == 'Control_R':
                        self._ctrl_pressed = True
                    elif event.keysym == 'Escape' and self._ctrl_pressed:
                        self.esc_callback()
                
                def on_key_release(event):
                    if event.keysym == 'Control_L' or event.keysym == 'Control_R':
                        self._ctrl_pressed = False
                
                self.gui_root.bind('<Control_L>', on_key_press)
                self.gui_root.bind('<Control_R>', on_key_press)
                self.gui_root.bind('<Control-Shift-L>', lambda e: None)  # Prevent Shift+Ctrl
                self.gui_root.bind('<Control-Shift-R>', lambda e: None)  # Prevent Shift+Ctrl
                self.gui_root.bind('<KeyRelease>', on_key_release)
                self.gui_root.bind('<Escape>', on_key_press)
                print("[!] Ctrl+ESC key binding added to GUI window")
            
            # Create profit/loss graph
            self.create_profit_loss_graph(self.gui_root)
            
            # Position window
            self.gui_root.geometry("+10+10")
            
            # Start GUI update loop
            self.update_gui()
            
            # Start the GUI main loop
            self.gui_root.mainloop()
        except Exception as e:
            print(f"[!] Error creating GUI: {e}")
    
    def on_window_close(self):
        """Handle window close event"""
        print("[!] GUI window closed - stopping bot...")
        self.stop_bot = True
    
    def esc_callback(self):
        """Ctrl+ESC key callback from GUI"""
        print("[!] Ctrl+ESC pressed from GUI - Stopping bot...")
        self.stop_bot = True
    
    def create_profit_loss_graph(self, parent):
        """Create profit/loss graph"""
        try:
            # Create single frame for profit/loss graph with red border
            main_frame = tk.Frame(parent, bg='#2d2d2d', relief=tk.SOLID, borderwidth=3, highlightbackground='red', highlightthickness=2)
            main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            # Add label for the graph
            label = tk.Label(main_frame, text="PROFIT/LOSS GRAPH", font=("Arial", 12, "bold"), 
                            bg='#2d2d2d', fg='#00ff00', relief=tk.RIDGE, borderwidth=2)
            label.pack(pady=5)
            
            # Create profit/loss graph with original size
            self.fig = Figure(figsize=(5, 3), dpi=100, facecolor='#2d2d2d')
            self.ax = self.fig.add_subplot(111, facecolor='#3d3d3d')
            
            # Add the white 0-line
            self.ax.axhline(0, color='white', linewidth=1.2, alpha=0.8)
            
            # Fixed intervals: Spins per 1, Profit also per 1
            self.ax.xaxis.set_major_locator(ticker.MultipleLocator(1))
            self.ax.yaxis.set_major_locator(ticker.MultipleLocator(1))
            
            # Make grid lighter because there are now many more lines
            self.ax.grid(True, which='both', color='white', linestyle='--', alpha=0.05)
            
            # Start range: directly 15 spins and $10 range visible
            self.ax.set_xlim(0, 15)
            self.ax.set_ylim(-5, 5)
            
            self.line, = self.ax.plot([], [], '#00ff00', linewidth=2)
            self.ax.set_ylabel('Profit ($)', color='white', fontsize=8)
            self.ax.tick_params(colors='white', labelsize=7)

            # Text feedback label
            self.stat_label = tk.Label(main_frame, text="Winst: $0.00 | Spins: 0", 
                                      font=("Consolas", 10, "bold"), bg='#2d2d2d', fg='#00ff00')
            self.stat_label.pack(pady=5)

            self.canvas = FigureCanvasTkAgg(self.fig, main_frame)
            self.canvas.draw()
            self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        except Exception as e:
            print(f"[!] Error creating profit/loss graph: {e}")
        
    def track_profit_loss(self, profit_change):
        self.round_count += 1
        print(f"[!] Graph Debug: RECEIVED profit_change=${profit_change:.2f}, current total_profit=${self.total_profit:.2f}")
        self.total_profit += profit_change
        self.profit_history.append(self.total_profit)
        self.round_history.append(self.round_count)
        print(f"[!] Graph Debug: UPDATED total_profit=${self.total_profit:.2f}, Round {self.round_count}")
        
        # Update GUI label immediately if available
        if hasattr(self, 'stat_label') and self.stat_label:
            try:
                color = '#00ff00' if self.total_profit >= 0 else '#ff4444'
                self.stat_label.config(text=f"Winst: ${self.total_profit:.2f} | Spins: {self.round_count}", fg=color)
                # Force immediate GUI update
                if hasattr(self, 'gui_root') and self.gui_root:
                    self.gui_root.update_idletasks()
            except:
                pass  # GUI might not be ready yet
        
        # Keep history limited but don't truncate too aggressively
        if len(self.profit_history) > 200:
            self.profit_history = self.profit_history[-200:]
            self.round_history = self.round_history[-200:]
        
        print(f"[!] Graph Debug: History size: {len(self.profit_history)} points")
            
    def update_gui(self):
        """Update GUI with latest data"""
        if self.gui_root:
            try:
                # Update profit/loss graph
                self.update_profit_loss_graph()
                
                # Schedule next update
                self.gui_root.after(200, self.update_gui)  # Update every 200ms for faster response
            except:
                pass  # GUI might be closed
                
    def update_profit_loss_graph(self):
        if len(self.profit_history) > 0 and hasattr(self, 'ax') and hasattr(self, 'canvas'):
            try:
                # Clear and redraw the entire axes to ensure line visibility
                self.ax.clear()
                
                # Recreate the basic setup after clearing
                self.ax.axhline(0, color='white', linewidth=1.2, alpha=0.8)
                self.ax.xaxis.set_major_locator(ticker.MultipleLocator(1))
                self.ax.yaxis.set_major_locator(ticker.MultipleLocator(1))
                self.ax.grid(True, which='both', color='white', linestyle='--', alpha=0.05)
                self.ax.set_facecolor('#3d3d3d')
                
                # Get current profit for color determination
                current_profit = self.profit_history[-1]
                
                # Determine line color based on current profit
                line_color = '#00ff00' if current_profit >= 0 else '#ff4444'
                
                # Plot the line with data and dynamic color
                self.ax.plot(self.round_history, self.profit_history, color=line_color, linewidth=2, marker='o', markersize=3)
                
                # X-axis: Show last 15 spins for detail
                view_size_x = 15
                current_round = self.round_history[-1]
                if current_round > view_size_x:
                    self.ax.set_xlim(current_round - view_size_x, current_round)
                else:
                    self.ax.set_xlim(0, max(view_size_x, current_round + 1))

                # Y-axis: Dynamic range around current profit with $10 window
                y_min = current_profit - 5
                y_max = current_profit + 5
                
                # Ensure 0-line is always visible when close to zero
                if abs(current_profit) < 5:
                    y_min, y_max = -5, 5
                
                # Add some padding to the range
                y_range = y_max - y_min
                if y_range < 10:
                    y_min -= 2
                    y_max += 2
                    
                self.ax.set_ylim(y_min, y_max)
                self.ax.set_ylabel('Profit ($)', color='white', fontsize=8)
                self.ax.tick_params(colors='white', labelsize=7)
                
                # Add title with current stats
                self.ax.set_title(f'Profit/Loss Tracking (Current: ${current_profit:.2f})', color='white', fontsize=10)
                
                self.canvas.draw()
                
            except Exception as e:
                print(f"[!] Error updating graph: {e}")
        else:
            # No data yet or GUI not ready
            pass

    def check_for_new_strategy(self):
        list_of_files = glob.glob(os.path.join(self.download_path, 'roulette_strategies*.json'))
        if not list_of_files: return False
        latest_file = max(list_of_files, key=os.path.getctime)
        if latest_file != self.current_strategy_file:
            data = self.load_json(latest_file)
            self.strategy_trackers = []
            self.all_strategies = data  # Store all strategies for switching
            default_strategy = None
            
            for s_data in data:
                # Check if there's a wait condition that should keep strategy inactive
                has_wait_condition = False
                for a in s_data.get('lossActions', []):
                    if a['type'] == 'after_x_losses_in_row':
                        has_wait_condition = True
                
                # Check if this strategy is set as default
                is_default = False
                for a in s_data.get('lossActions', []):
                    if a['type'] == 'set_as_default':
                        is_default = True
                        default_strategy = s_data.get('title', 'Unknown')
                
                self.strategy_trackers.append({
                    "base_copy": copy.deepcopy(s_data),
                    "current_data": s_data,
                    "losses_in_row": 0,
                    "wins_in_row": 0,
                    "consecutive_losses": 0,
                    "consecutive_wins": 0,
                    "total_loss": 0.0,
                    "total_win": 0.0,
                    "is_active": not has_wait_condition and is_default,  # Active only if no wait condition AND is default
                    "is_stopped": False,
                    "target_strategy": None,
                    "last_bet_amount": 0.0
                })
            self.current_strategy_file = latest_file
            self.first_run_done = False
            
            # Print strategy status
            active_count = sum(1 for s in self.strategy_trackers if s['is_active'])
            inactive_count = len(self.strategy_trackers) - active_count
            print(f"[!] {len(data)} strategies loaded. Active: {active_count}, Inactive: {inactive_count}")
            
            if default_strategy:
                print(f"[!] Default strategy set to: {default_strategy}")
            else:
                print("[!] No default strategy found - all strategies will wait for triggers")
            
            # Print details for debugging
            for s in self.strategy_trackers:
                title = s['base_copy'].get('title', 'Unknown')
                status = "ACTIVE" if s['is_active'] else "INACTIVE (waiting for trigger)"
                print(f"    - {title}: {status}")
            
            return True
        return False

    def check_win(self, strategy_bets, n):
        n = int(n)
        reds = [1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36]
        blacks = [2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35]
        
        print(f"[!] Debug: check_win called with number {n}")
        
        for bet in strategy_bets:
            s = str(bet['square']).lower()
            print(f"[!] Debug: Checking bet '{s}' against number {n}")
            
            # Direct number match
            if str(n) == s: 
                print(f"[!] Debug: DIRECT MATCH - {s} == {n} = WIN")
                return True
            
            # Outside bets
            if s == "red" and n in reds: 
                print(f"[!] Debug: RED BET - {s} WIN (number {n} is red)")
                return True
            if s == "black" and n in blacks: 
                print(f"[!] Debug: BLACK BET - {s} WIN (number {n} is black)")
                return True
            if s == "even" and n != 0 and n % 2 == 0: 
                print(f"[!] Debug: EVEN BET - {s} WIN (number {n} is even)")
                return True
            if s == "odd" and n % 2 != 0: 
                print(f"[!] Debug: ODD BET - {s} WIN (number {n} is odd)")
                return True
            if s == "low" or s == "1-18": 
                if 1 <= n <= 18:
                    print(f"[!] Debug: LOW BET - {s} WIN (number {n} is low)")
                    return True
            if s == "high" or s == "19-36": 
                if 19 <= n <= 36:
                    print(f"[!] Debug: HIGH BET - {s} WIN (number {n} is high)")
                    return True
            
            # Dozen bets
            if s in ["dozen-1", "dozen-2", "dozen-3", "1st 12", "2nd 12", "3rd 12"]:
                if s in ["dozen-1", "1st 12"]:
                    if 1 <= n <= 12:
                        print(f"[!] Debug: DOZEN-1 BET - {s} WIN (number {n} is in 1-12)")
                        return True
                elif s in ["dozen-2", "2nd 12"]:
                    if 13 <= n <= 24:
                        print(f"[!] Debug: DOZEN-2 BET - {s} WIN (number {n} is in 13-24)")
                        return True
                elif s in ["dozen-3", "3rd 12"]:
                    if 25 <= n <= 36:
                        print(f"[!] Debug: DOZEN-3 BET - {s} WIN (number {n} is in 25-36)")
                        return True
            
            # Street bets (e.g., "street-1-2-3")
            if s.startswith('street-'):
                numbers = s.replace('street-', '').split('-')
                if str(n) in numbers: 
                    print(f"[!] Debug: STREET BET - {s} WIN (number {n} is in {numbers})")
                    return True
            
            # Double street bets (e.g., "double-street-4-5-6-7-8-9")
            if s.startswith('double-street-'):
                numbers = s.replace('double-street-', '').split('-')
                if str(n) in numbers: 
                    print(f"[!] Debug: DOUBLE-STREET BET - {s} WIN (number {n} is in {numbers})")
                    return True
            # Handle double street bets with underscores (config file naming)
            elif s.startswith('double_street_'):
                numbers = s.replace('double_street_', '').split('_')
                if str(n) in numbers: 
                    print(f"[!] Debug: DOUBLE-STREET BET - {s} WIN (number {n} is in {numbers})")
                    return True
                    
            # Column bets
            if s in ["col-1", "col-2", "col-3", "col1", "col2", "col3"]:
                if s in ["col-1", "col1"]:
                    if n % 3 == 1 and 1 <= n <= 36:
                        print(f"[!] Debug: COLUMN-1 BET - {s} WIN (number {n} is in column 1)")
                        return True
                elif s in ["col-2", "col2"]:
                    if n % 3 == 2 and 1 <= n <= 36:
                        print(f"[!] Debug: COLUMN-2 BET - {s} WIN (number {n} is in column 2)")
                        return True
                elif s in ["col-3", "col3"]:
                    if n % 3 == 0 and 1 <= n <= 36:
                        print(f"[!] Debug: COLUMN-3 BET - {s} WIN (number {n} is in column 3)")
                        return True
                else:
                    print(f"[!] Debug: Unknown column bet type: {s}")
                    return False

        return False
        
        # Single number
        if s.isdigit() and 0 <= int(s) <= 36:
            return 36
        
        # Outside bets
        if s in ['red', 'black', 'even', 'odd', 'low', 'high', '1-18', '19-36']:
            return 2
        if s in ['dozen-1', 'dozen-2', 'dozen-3', '1st 12', '2nd 12', '3rd 12']:
            return 3
        if s in ['col-1', 'col-2', 'col-3', 'col1', 'col2', 'col3']:
            return 3
        
        # Streets / Lines
        if s.startswith('street-'):
            return 12
        if s.startswith('double-street-'):
            return 6
        if 'trio' in s:
            return 12
        if 'basket' in s:
            return 9
        
        return 1

    def normalize_bet_type(self, bet_type):
        """Convert bet types from JSON to config format - HANDLE BOTH NAMING CONVENTIONS"""
        bet_type = str(bet_type).lower()
        
        # Direct number matches (0-36)
        if bet_type.isdigit() and 0 <= int(bet_type) <= 36:
            return bet_type
        
        # Handle street conversions
        if 'street-' in bet_type:
            return bet_type.replace('street-', 'street_').replace('-', '_')
        
        # Handle double street conversions - HTML TOOL NAMING
        html_tool_mapping = {
            'double-street-1-2-3-4-5-6': 'double_street_1_2_3_4_5_6',
            'double-street-4-5-6-7-8-9': 'double_street_4_5_6_7_8_9',
            'double-street-7-8-9-10-11-12': 'double_street_7_8_9_10_11_12',
            'double-street-10-11-12-13-14-15': 'double_street_10_11_12_13_14_15',
            'double-street-13-14-15-16-17-18': 'double_street_13_14_15_16_17_18',
            'double-street-16-17-18-19-20-21': 'double_street_16_17_18_19_20_21',
            'double-street-19-20-21-22-23-24': 'double_street_19_20_21_22_23_24',
            'double-street-22-23-24-25-26-27': 'double_street_22_23_24_25_26_27',
            'double-street-25-26-27-28-29-30': 'double_street_25_26_27_28_29_30',
            'double-street-28-29-30-31-32-33': 'double_street_28_29_30_31_32_33',
            'double-street-31-32-33-34-35-36': 'double_street_31_32_33_34_35_36'
        }
        
        # Handle double street conversions - CONFIG FILE NAMING (MATCH YOUR CONFIG EXACTLY)
        config_file_mapping = {
            'double-street-1-2-3-4-5-6': 'double_street_1_2_3_4_5_6',
            'double-street-4-5-6-7-8-9': 'double_street_4_5_6_7_8_9',
            'double-street-7-8-9-10-11-12': 'double_street_7_8_9_10_11_12',
            'double-street-10-11-12-13-14-15': 'double_street_10_11_12_13_14_15',
            'double-street-13-14-15-16-17-18': 'double_street_13_14_15_16_17_18',
            'double-street-16-17-18-19-20-21': 'double_street_16_17_18_19_20_21',
            'double-street-19-20-21-22-23-24': 'double_street_19_20_21_22_23_24',
            'double-street-22-23-24-25-26-27': 'double_street_22_23_24_25_26_27',
            'double-street-25-26-27-28-29-30': 'double_street_25_26_27_28_29_30',
            'double-street-28-29-30-31-32-33': 'double_street_28_29_30_31_32_33',
            'double-street-31-32-33-34-35-36': 'double_street_31_32_33_34_35_36'
        }
        
        # Try HTML tool naming first
        if bet_type in html_tool_mapping:
            return html_tool_mapping[bet_type]
        
        # Fallback to config file naming
        if bet_type in config_file_mapping:
            return config_file_mapping[bet_type]
        
        # Outside bets
        outside_bets = {
            'red': 'red', 'black': 'black', 'even': 'even', 'odd': 'odd',
            '1st 12': '1st 12', '2nd 12': '2nd 12', '3rd 12': '3rd 12',
            'dozen-1': 'dozen-1', 'dozen-2': 'dozen-2', 'dozen-3': 'dozen-3',
            '1-18': '1-18', '19-36': '19-36', 'col1': 'col1', 'col2': 'col2', 'col3': 'col3',
            'low': 'low', 'high': 'high', 'l1': 'low', 'h1': 'high'  # Add L1/H1 mappings
        }
        
        if bet_type in outside_bets:
            return outside_bets[bet_type]
        
        # Special bets
        special_bets = {
            'trio-0-1-2': 'trio_0_1_2',
            'trio-0-2-3': 'trio_0_2_3',
            'basket-0-1-2-3': 'basket_0_1_2_3'
        }
        
        if bet_type in special_bets:
            return special_bets[bet_type]
        
        # Racetrack bets
        racetrack_bets = {
            'tier': 'tier',
            'orphelins': 'orphelins',
            'voisins': 'voisins',
            'zero_game': 'zero_game'
        }
        
        if bet_type in racetrack_bets:
            return racetrack_bets[bet_type]
        
        # Split bets (handle format like "1/2")
        if '/' in bet_type:
            return bet_type.replace('/', '/')
        
        # If no conversion needed, return as-is
        return bet_type

    def handle_multiply_bet(self, s_obj, multiplier):
        """Multiply base bet amounts"""
        base_bets = s_obj['base_copy']['bets']
        for bet in base_bets:
            for chip in bet['chips']:
                chip['value'] = float(chip['value']) * multiplier
        s_obj['current_data']['bets'] = copy.deepcopy(base_bets)

    def handle_multiply_current_bet(self, s_obj, multiplier):
        """Multiply current bet amounts"""
        current_bets = s_obj['current_data']['bets']
        for bet in current_bets:
            for chip in bet['chips']:
                chip['value'] = float(chip['value']) * multiplier

    def handle_unit_adjustment(self, s_obj, units, action_type):
        """Handle unit increase/decrease actions"""
        current_bets = s_obj['current_data']['bets']
        
        for bet in current_bets:
            for chip in bet['chips']:
                if action_type == 'increase':
                    chip['value'] = float(chip['value']) + units
                elif action_type == 'decrease':
                    chip['value'] = max(0.1, float(chip['value']) - units)  # Minimum 0.1

    def handle_switch_to_strategy(self, s_obj, target_strategy_name):
        """Switch to a different strategy - with round lock to prevent multiple switches"""
        # Prevent multiple switches in the same round
        if self.strategy_switched_this_round:
            return
        
        # Find the target strategy
        target_strategy = None
        for strategy in self.all_strategies:
            if strategy.get('title', '').lower() == target_strategy_name.lower():
                target_strategy = strategy
                break
        
        if target_strategy:
            # Mark that we've switched strategies this round
            self.strategy_switched_this_round = True
            
            # Deactivate current strategy
            s_obj['is_active'] = False
            s_obj['consecutive_losses'] = 0
            s_obj['consecutive_wins'] = 0
            s_obj['losses_in_row'] = 0
            s_obj['wins_in_row'] = 0
            
            # Find and activate target strategy
            for target_s_obj in self.strategy_trackers:
                if target_s_obj['base_copy'].get('title', '').lower() == target_strategy_name.lower():
                    target_s_obj['current_data'] = copy.deepcopy(target_s_obj['base_copy'])
                    target_s_obj['is_active'] = True
                    target_s_obj['consecutive_losses'] = 0
                    target_s_obj['consecutive_wins'] = 0
                    target_s_obj['losses_in_row'] = 0
                    target_s_obj['wins_in_row'] = 0
                    target_s_obj['is_stopped'] = False
                    break
            
            # Clear rebet state to prevent unwanted rebet after switching
            self.can_use_rebet = False
            self.last_bet_totals = {}
        else:
            print(f"[!] Strategy '{target_strategy_name}' not found")

    def handle_start_highest_winrate(self, s_obj):
        """Start strategy with highest win rate (placeholder)"""
        # This would require win rate tracking - for now, just reset to base
        s_obj['current_data'] = copy.deepcopy(s_obj['base_copy'])
        print("[!] Starting strategy with highest win rate (reset to base)")

    def handle_stop_strategy(self, s_obj):
        """Stop the current strategy and reset triggers"""
        s_obj['is_stopped'] = True
        s_obj['is_active'] = False
        s_obj['consecutive_losses'] = 0  # Reset loss counter for re-activation
        s_obj['consecutive_wins'] = 0    # Reset win counter for re-activation
        # Clear rebet state to prevent unwanted rebet after stopping
        self.can_use_rebet = False
        self.last_bet_totals = {}
        print(f"[!] Strategy stopped: {s_obj['base_copy'].get('title', 'Unknown')}")

    def handle_restart_strategy(self, s_obj):
        """Restart strategy - reset all triggers and make inactive but ready to activate"""
        s_obj['is_stopped'] = False
        s_obj['is_active'] = False  # Keep inactive until losses trigger activation
        s_obj['consecutive_losses'] = 0  # Reset loss counter
        s_obj['consecutive_wins'] = 0    # Reset win counter
        s_obj['losses_in_row'] = 0
        s_obj['wins_in_row'] = 0
        s_obj['total_loss'] = 0.0
        s_obj['total_win'] = 0.0
        # Reset to base bets
        s_obj['current_data'] = copy.deepcopy(s_obj['base_copy'])
        print(f"[!] Strategy restarted: {s_obj['base_copy'].get('title', 'Unknown')}")

    def handle_start_after_losses(self, s_obj, min_losses):
        """Start strategy after minimal losses if no other strategy is in progression"""
        # Check if any other strategy is currently active (in progression)
        other_active = any(s['is_active'] and s != s_obj for s in self.strategy_trackers)
        
        if not other_active and s_obj['consecutive_losses'] >= min_losses:
            s_obj['is_active'] = True
            s_obj['consecutive_losses'] = 0  # Reset counter after activation
            print(f"[!] Strategy '{s_obj['base_copy'].get('title', 'Unknown')}' activated after {min_losses} losses")
        else:
            print(f"[!] Cannot start '{s_obj['base_copy'].get('title', 'Unknown')}' - other strategies active or insufficient losses")

    def handle_stop_on_loss(self, s_obj, max_loss):
        """Stop strategy when loss exceeds specified amount"""
        if s_obj['total_loss'] >= max_loss:
            s_obj['is_stopped'] = True
            s_obj['is_active'] = False
            print(f"[!] Strategy '{s_obj['base_copy'].get('title', 'Unknown')}' stopped - loss exceeded ${max_loss}")
        else:
            print(f"[!] Loss threshold not met: ${s_obj['total_loss']:.2f} < ${max_loss}")

    def handle_stop_on_win(self, s_obj, max_win):
        """Stop strategy when profit exceeds specified amount"""
        if s_obj['total_win'] >= max_win:
            s_obj['is_stopped'] = True
            s_obj['is_active'] = False
            print(f"[!] Strategy '{s_obj['base_copy'].get('title', 'Unknown')}' stopped - profit exceeded ${max_win}")
        else:
            print(f"[!] Win threshold not met: ${s_obj['total_win']:.2f} < ${max_win}")

    def handle_start_current_strategy(self, s_obj):
        """Start/restart the current strategy"""
        s_obj['is_stopped'] = False
        s_obj['is_active'] = True
        s_obj['losses_in_row'] = 0
        s_obj['wins_in_row'] = 0
        s_obj['consecutive_losses'] = 0
        s_obj['consecutive_wins'] = 0
        s_obj['current_data'] = copy.deepcopy(s_obj['base_copy'])
        print(f"[!] Strategy started: {s_obj['base_copy'].get('title', 'Unknown')}")

    def handle_set_as_default(self, s_obj):
        """Handle set_as_default action - this is processed during initialization"""
        # This action is handled during strategy loading, not during runtime
        pass

    def handle_conditional_actions(self, s_obj, action):
        """Handle nested actions from conditional triggers"""
        params = action.get('params', {})
        nested_params = action.get('nestedParams', {})
        nested_action = params.get('action') or nested_params.get('action', {}).get('action')
        target_strategy = params.get('targetStrategy') or nested_params.get('action', {}).get('targetStrategy')
        if nested_action:
            action_mapping = {
                'start current strategy': 'start_current_strategy',
                'stop strategy': 'stop_strategy',
                'restart strategy': 'restart_strategy',
                'switch to strategy': 'switch_to_strategy',
                'reset to base': 'reset_to_base',
                'multiply current bet': 'multiply_current_bet',
                'increase # unit on current bet': 'increase_units_to_current_bet',
                'decrease # unit on current bet': 'decrease_units_to_current_bet'
            }
            mapped_action_type = action_mapping.get(nested_action, nested_action)
            temp_action = {'type': mapped_action_type}
            if target_strategy and mapped_action_type == 'switch_to_strategy':
                temp_action['params'] = {'targetStrategy': target_strategy}
            
            self.handle_single_action(s_obj, temp_action)

    def handle_single_action(self, s_obj, action):
        """Handle a single action"""
        action_type = action['type']
        params = action.get('params', {})
        
        print(f"[!] Executing action: {action_type} with params: {params}")
        
        # Betting Actions
        if action_type == 'multiply_bet':
            multiplier = params.get('multiplier', 2)
            self.handle_multiply_bet(s_obj, multiplier)
            
        elif action_type == 'multiply_current_bet':
            multiplier = params.get('multiplier', 2)
            self.handle_multiply_current_bet(s_obj, multiplier)
            
        elif action_type == 'reset_to_base':
            s_obj['current_data'] = copy.deepcopy(s_obj['base_copy'])
            # Reset activity state
            has_wait = any(a['type'] == 'after_x_losses_in_row' for a in s_obj['base_copy'].get('lossActions', []))
            s_obj['is_active'] = not has_wait
            s_obj['consecutive_losses'] = 0
            s_obj['consecutive_wins'] = 0
            
        # Unit Management Actions
        elif action_type in ['increase_units_to_losing_bet', 'increase_units_to_current_bet', 'increase_units_to_winning_bet']:
            units = params.get('units', 1)
            self.handle_unit_adjustment(s_obj, units, 'increase')
            
        elif action_type in ['decrease_units_to_losing_bet', 'decrease_units_to_current_bet', 'decrease_units_to_winning_bet']:
            units = params.get('units', 1)
            self.handle_unit_adjustment(s_obj, units, 'decrease')
            
        # Strategy Control Actions
        elif action_type == 'switch_to_strategy':
            target_strategy = params.get('targetStrategy', '')
            self.handle_switch_to_strategy(s_obj, target_strategy)
            
        elif action_type == 'start_highest_winrate':
            self.handle_start_highest_winrate(s_obj)
            
        elif action_type == 'start_current_strategy':
            self.handle_start_current_strategy(s_obj)
            
        elif action_type == 'stop_strategy':
            self.handle_stop_strategy(s_obj)
            
        elif action_type == 'restart_strategy':
            self.handle_restart_strategy(s_obj)
            
        elif action_type == 'set_as_default':
            self.handle_set_as_default(s_obj)
            
        elif action_type == 'start_after_losses':
            min_losses = params.get('minLosses', 7)
            self.handle_start_after_losses(s_obj, min_losses)
            
        elif action_type == 'stop_on_loss':
            max_loss = params.get('maxLossAmount', 100)
            self.handle_stop_on_loss(s_obj, max_loss)
            
        elif action_type == 'stop_on_win':
            max_win = params.get('maxWinAmount', 100)
            self.handle_stop_on_win(s_obj, max_win)
            
        # Special Actions
        elif action_type == 'winning_all_bets_reset':
            # Handle nested action for winning all bets
            self.handle_conditional_actions(s_obj, action)
            
        elif action_type == 'stop_session':
            print("[!] Stop session triggered - ending bot session")
            # Stop all strategies
            for s in self.strategy_trackers:
                s['is_stopped'] = True
                s['is_active'] = False
            print("[!] All strategies stopped")
            
        # Conditional Actions (these are handled in the main logic, but have nested actions)
        elif action_type in ['on_every_loss', 'on_every_win', 'on_x_loss', 'on_x_win', 'after_x_losses_in_row', 'after_x_wins_in_row', 
                              'every_streak_of_losses', 'first_streak_of_losses', 'streak_greater_than_losses', 'streak_lower_than_losses',
                              'every_streak_of_wins', 'first_streak_of_wins', 'streak_greater_than_wins', 'streak_lower_than_wins',
                              'every_streak_of_bets', 'first_streak_of_bets', 'streak_greater_than_bets', 'streak_lower_than_bets']:
            # These are handled in the main conditional logic
            pass
            
        else:
            print(f"[!] Unknown action type: {action_type}")

    def handle_actions(self, s_obj, action_list_name):
        """Handle all actions in an action list"""
        actions = s_obj['current_data'].get(action_list_name, [])
        
        for action in actions:
            if s_obj['is_stopped']:
                break  # Don't execute actions if strategy is stopped
                
            self.handle_single_action(s_obj, action)
            
    def calculate_bet_amount(self, bets):
        """Calculate total amount bet across all positions"""
        total = 0
        for bet in bets:
            total += sum(float(c['value']) for c in bet['chips'])
        return total

    def get_multiplier(self, square):
        s = str(square).lower()
        # Single number
        if s.isdigit(): return 36
        # Outside bets
        if s in ['red', 'black', 'even', 'odd', '1-18', '19-36', 'low', 'high']: return 2
        if s in ['col1', 'col2', 'col3', '1st 12', '2nd 12', '3rd 12', 'dozen-1', 'dozen-2', 'dozen-3']: return 3
        # Streets / Lines
        if s.startswith('street-'): return 12
        if s.startswith('double-street-') or s.startswith('double_street_'): return 6
        if 'trio' in s: return 12
        if 'basket' in s: return 9
        return 1 # Fallback
            

    def check_conditional_triggers(self, s_obj, won):
        """Check and handle conditional action triggers"""
        
        # Check on_x_loss and on_every_loss actions
        if not won:
            s_obj['consecutive_losses'] += 1
            s_obj['consecutive_wins'] = 0
            
            for action in s_obj['current_data'].get('lossActions', []):
                if action['type'] == 'on_every_loss':
                    loss_count = action.get('params', {}).get('lossCount', 1)
                    if s_obj['consecutive_losses'] % loss_count == 0:
                        print(f"[!] Triggered every {loss_count} losses")
                        self.handle_conditional_actions(s_obj, action)
                elif action['type'] == 'on_x_loss':
                    loss_count = action.get('params', {}).get('lossCount', 3)
                    if s_obj['consecutive_losses'] >= loss_count:
                        print(f"[!] Triggered on loss #{loss_count}")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'after_x_losses_in_row':
                    min_losses = action.get('params', {}).get('minLosses', 2)
                    if s_obj['consecutive_losses'] >= min_losses:
                        print(f"[!] Triggered after minimal #{min_losses} losses in a row")
                        self.handle_conditional_actions(s_obj, action)
                        # Check if strategy should be activated
                        nested_action = action.get('params', {}).get('action')
                        if nested_action == 'start current strategy':
                            s_obj['is_active'] = True
                            
                # Streak-related loss actions
                elif action['type'] == 'every_streak_of_losses':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_losses'] % streak_count == 0:
                        print(f"[!] Triggered every {streak_count} losses in a streak")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'first_streak_of_losses':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_losses'] == streak_count and s_obj['consecutive_losses'] > 0:
                        print(f"[!] Triggered first streak of {streak_count} losses")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'streak_greater_than_losses':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_losses'] > streak_count:
                        print(f"[!] Triggered on streak greater than {streak_count} losses")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'streak_lower_than_losses':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_losses'] < streak_count and s_obj['consecutive_losses'] > 0:
                        print(f"[!] Triggered on streak lower than {streak_count} losses")
                        self.handle_conditional_actions(s_obj, action)
                            
        # Check on_x_win and on_every_win actions
        if won:
            s_obj['consecutive_wins'] += 1
            s_obj['consecutive_losses'] = 0
            
            for action in s_obj['current_data'].get('winActions', []):
                if action['type'] == 'on_every_win':
                    win_count = action.get('params', {}).get('winCount', 1)
                    if s_obj['consecutive_wins'] % win_count == 0:
                        print(f"[!] Triggered every {win_count} wins")
                        self.handle_conditional_actions(s_obj, action)
                elif action['type'] == 'on_x_win':
                    win_count = action.get('params', {}).get('winCount', 3)
                    if s_obj['consecutive_wins'] >= win_count:
                        print(f"[!] Triggered on win #{win_count}")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'after_x_wins_in_row':
                    min_wins = action.get('params', {}).get('minWins', 2)
                    if s_obj['consecutive_wins'] >= min_wins:
                        print(f"[!] Triggered after minimal #{min_wins} wins in a row")
                        self.handle_conditional_actions(s_obj, action)
                        
                # Streak-related win actions
                elif action['type'] == 'every_streak_of_wins':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_wins'] % streak_count == 0:
                        print(f"[!] Triggered every {streak_count} wins in a streak")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'first_streak_of_wins':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_wins'] == streak_count and s_obj['consecutive_wins'] > 0:
                        print(f"[!] Triggered first streak of {streak_count} wins")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'streak_greater_than_wins':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_wins'] > streak_count:
                        print(f"[!] Triggered on streak greater than {streak_count} wins")
                        self.handle_conditional_actions(s_obj, action)
                        
                elif action['type'] == 'streak_lower_than_wins':
                    streak_count = action.get('params', {}).get('count', 1)
                    if s_obj['consecutive_wins'] < streak_count and s_obj['consecutive_wins'] > 0:
                        print(f"[!] Triggered on streak lower than {streak_count} wins")
                        self.handle_conditional_actions(s_obj, action)
                        
        # Bet-related streak actions
        for action in s_obj['current_data'].get('betActions', []):
            if action['type'] == 'every_streak_of_bets':
                streak_count = action.get('params', {}).get('count', 1)
                if (s_obj['consecutive_wins'] + s_obj['consecutive_losses']) % streak_count == 0:
                    print(f"[!] Triggered every {streak_count} bets in a streak")
                    self.handle_conditional_actions(s_obj, action)
                    
            elif action['type'] == 'first_streak_of_bets':
                streak_count = action.get('params', {}).get('count', 1)
                if (s_obj['consecutive_wins'] + s_obj['consecutive_losses']) == streak_count and (s_obj['consecutive_wins'] + s_obj['consecutive_losses']) > 0:
                    print(f"[!] Triggered first streak of {streak_count} bets")
                    self.handle_conditional_actions(s_obj, action)
                    
            elif action['type'] == 'streak_greater_than_bets':
                streak_count = action.get('params', {}).get('count', 1)
                if (s_obj['consecutive_wins'] + s_obj['consecutive_losses']) > streak_count:
                    print(f"[!] Triggered on streak greater than {streak_count} bets")
                    self.handle_conditional_actions(s_obj, action)
                    
            elif action['type'] == 'streak_lower_than_bets':
                streak_count = action.get('params', {}).get('count', 1)
                if (s_obj['consecutive_wins'] + s_obj['consecutive_losses']) < streak_count and (s_obj['consecutive_wins'] + s_obj['consecutive_losses']) > 0:
                    print(f"[!] Triggered on streak lower than {streak_count} bets")
                    self.handle_conditional_actions(s_obj, action)

    def check_stop_conditions(self, s_obj):
        """Check stop_on_loss and stop_on_win conditions"""
        
        # Check stop_on_loss
        for action in s_obj['current_data'].get('lossActions', []):
            if action['type'] == 'stop_on_loss':
                max_loss = action.get('params', {}).get('maxLossAmount', 100)
                if s_obj['total_loss'] >= max_loss:
                    print(f"[!] Stop condition met: Loss exceeded {max_loss}")
                    self.handle_stop_strategy(s_obj)
                    return True
                    
        # Check stop_on_win
        for action in s_obj['current_data'].get('winActions', []):
            if action['type'] == 'stop_on_win':
                max_win = action.get('params', {}).get('maxWinAmount', 100)
                if s_obj['total_win'] >= max_win:
                    print(f"[!] Stop condition met: Profit exceeded {max_win}")
                    self.handle_stop_strategy(s_obj)
                    return True
                    
        return False

    def execute_combined_bets(self):
        """Execute combined bets from ACTIVE strategies only - MEDIUM SPEED"""
        totals = {}
        found_any_active = False
        
        for s in self.strategy_trackers:
            if s['is_active'] and not s['is_stopped']:
                found_any_active = True
                for bet in s['current_data']['bets']:
                    sq = self.normalize_bet_type(bet['square'])
                    val = sum(float(c['value']) for c in bet['chips'])
                    totals[sq] = totals.get(sq, 0) + val
        
        if not found_any_active or not totals:
            print("[!] No active strategies with bets found.")
            return False

        print(f"[!] Placing bets on {len(totals)} positions:")
        for square, amount in totals.items():
            print(f"    - {square}: ${amount:.2f}")
        
        # Check if we can use rebet (same bets as before)
        if self.can_use_rebet and totals == self.last_bet_totals:
            print("[!] Using REBET - same bets as previous round")
            if 'rebet_button' in self.coords['ui']:
                self.hc.move(self.coords['ui']['rebet_button'], 0.4)
                pyautogui.click()
                time.sleep(0.4)
                print("[!] Rebet clicked successfully!")
                return True
            else:
                print("[!] Rebet button not found in config_coords.json")
        
        # Store current bets for next round
        self.last_bet_totals = totals.copy()
        self.can_use_rebet = True
        
        # Find coordinates for all positions
        positions = {}
        for square, amount in totals.items():
            target = None
            for cat in self.coords:
                if str(square) in self.coords[cat]:
                    target = self.coords[cat][str(square)]
                    break
            if target:
                positions[square] = target
        
        # Get chips and place all bets
        available_chips = {float(k): v for k, v in self.coords['chips'].items()}
        sorted_chips = sorted(available_chips.keys(), reverse=True)
        current_chip = None

        # Process each position
        for square, amount in totals.items():
            target = positions.get(square)
            if not target:
                print(f"[!] ERROR: Position '{square}' not found in config_coords.json")
                continue
            
            rem = round(amount, 2)
            uitbetaling = 0  # Reset uitbetaling for each new round
            for cv in sorted_chips:
                while rem >= cv:
                    if current_chip != cv:
                        self.hc.move(available_chips[cv], 0.4)  # Medium chip selection
                        pyautogui.click()
                        current_chip = cv
                        time.sleep(0.1)  # Fast chip change delay
                    self.hc.move(target, 0.15)  # Fast bet placement
                    pyautogui.click()
                    rem = round(rem - cv, 2)
                    time.sleep(0.08)  # Fast bet placement delay
            time.sleep(0.08)  # Fast delay between positions
        return True

    def get_last_number(self):
        """Get the last number from roulette history - ENHANCED OCR WITH IMPROVED PREPROCESSING"""
        try:
            screenshot = pyautogui.screenshot(region=HISTORY_REGION)
            
            # Enhanced preprocessing for better OCR
            screenshot = screenshot.convert('L')  # Convert to grayscale
            
            # Apply contrast enhancement
            from PIL import ImageEnhance
            enhancer = ImageEnhance.Contrast(screenshot)
            screenshot = enhancer.enhance(2.0)  # Increase contrast
            
            # Apply sharpening
            enhancer = ImageEnhance.Sharpness(screenshot)
            screenshot = enhancer.enhance(2.0)  # Sharpen the image
            
            # Resize for better OCR (4x upscaling for better detail)
            screenshot = screenshot.resize((screenshot.width * 4, screenshot.height * 4))
            
            # Binarize the image (convert to pure black and white)
            threshold = 128
            screenshot = screenshot.point(lambda p: 255 if p > threshold else 0)
            
            # Try multiple configs in order of reliability
            configs = [
                '--psm 8 -c tessedit_char_whitelist=0123456789',  # Single word
                '--psm 7 -c tessedit_char_whitelist=0123456789',  # Single line
                '--psm 6 -c tessedit_char_whitelist=0123456789',  # Uniform block
                '--psm 13 -c tessedit_char_whitelist=0123456789', # Raw line
                '--psm 10 -c tessedit_char_whitelist=0123456789', # Single character
                '--psm 9 -c tessedit_char_whitelist=0123456789',  # Single word
                '--psm 11 -c tessedit_char_whitelist=0123456789', # Sparse text
                '--psm 12 -c tessedit_char_whitelist=0123456789'  # Sparse text with OSD
            ]
            
            # Store all successful readings for verification
            successful_readings = []
            config_scores = {}  # Track confidence per config
            
            for i, config in enumerate(configs):
                text = pytesseract.image_to_string(screenshot, config=config)
                clean_text = text.strip()
                
                if clean_text.isdigit():
                    # Validate number is reasonable (0-36)
                    num = int(clean_text)
                    if 0 <= num <= 36:
                        successful_readings.append(num)
                        config_scores[i] = num
                        print(f"[!] OCR config {i+1}: Read {num}")
            
            # Enhanced validation with temporal consistency
            if successful_readings:
                from collections import Counter
                most_common = Counter(successful_readings).most_common(1)[0][0]
                confidence = Counter(successful_readings).most_common(1)[0][1]
                
                print(f"[!] OCR Results: {successful_readings}")
                print(f"[!] Most common: {most_common} (confidence: {confidence}/{len(configs)})")
                
                # Additional validation: Check if result makes sense historically
                if hasattr(self, 'last_spin_result') and self.last_spin_result is not None:
                    # If we get the same number multiple times in a row, be suspicious
                    if successful_readings.count(most_common) == len(successful_readings) and most_common == self.last_spin_result:
                        print(f"[!] Warning: Same number {most_common} detected again - lower confidence")
                
                # Only accept if we have reasonable confidence (at least 2 readings agree)
                if confidence >= 2 or len(successful_readings) >= 3:
                    return most_common
                else:
                    print(f"[!] Low confidence OCR result: {most_common} - using fallback")
                
                # Store OCR result for HTML tool
                self.add_ocr_result(most_common)
                print(f"[!] 🎯 Final OCR result: {most_common}")
                return most_common
            
            return None
            
        except Exception as e:
            print(f"OCR Error: {e}")
            return None

if __name__ == "__main__":
    bot = RouletteBot()
    last_val = None
    
    print("[!] Roulette Bot Started - Waiting for strategies...")
    print("[!] Starting in 5 seconds...")
    time.sleep(5)
    print("[!] Bot is now active!")
    
    # Start HTTP server for OCR results
    bot.start_http_server()
    
    # Create GUI windows for visualization
    bot.create_gui_windows()
    
    # Give GUI time to initialize
    time.sleep(1)
    print("[!] GUI windows created")
    
    # Load strategies and check for default
    bot.check_for_new_strategy()
    
    # If no default strategy was found, activate the first strategy without wait conditions
    if not any(s['is_active'] for s in bot.strategy_trackers):
        for s in bot.strategy_trackers:
            has_wait_condition = any(a['type'] == 'after_x_losses_in_row' for a in s['base_copy'].get('lossActions', []))
            if not has_wait_condition:
                s['is_active'] = True
                print(f"[!] No default strategy found - activating '{s['base_copy'].get('title', 'Unknown')}' as fallback")
                break
    
    while not bot.stop_bot:
        sx, sy = bot.coords['ui']['spin_button']
        
        knop = None
        try:
            knop = pyautogui.locateOnScreen(bot.tafel_marker, region=(sx-150, sy-150, 300, 300), confidence=0.6)
        except:
            knop = None

        if not knop:
            bot.knop_was_weg = True
        
        if knop:
            if not bot.first_run_done or bot.knop_was_weg:
                print("\n[!] Table ready. Reading number...")
                current_val = bot.get_last_number()
                
                if current_val is not None:
                    if not bot.first_run_done:
                        print(f"[!] Start number recognized: {current_val}. First round - placing bets.")
                        bot.first_run_done = True
                        bot.knop_was_weg = False
                        last_val = current_val
                    else:
                        print(f"[!] Round result: {current_val}. Updating strategies...")
                        
                        # Reset strategy switch lock for new round
                        bot.strategy_switched_this_round = False
                        
                        # Calculate total profit/loss from all active strategies
                        total_round_profit = 0
                        
                        # Process each strategy - ONLY ONE ACTIVE STRATEGY AT A TIME
                        active_strategy = None
                        for s in bot.strategy_trackers:
                            if s['is_active'] and not s['is_stopped']:
                                active_strategy = s
                                break  # Only process the first active strategy
                        
                        if active_strategy:
                            s = active_strategy
                            print(f"[!] Debug: Processing strategy {s['base_copy'].get('title', 'Unknown')} (only active strategy)")
                            
                            bet_amount = bot.calculate_bet_amount(s['current_data']['bets'])
                            won = bot.check_win(s['current_data']['bets'], current_val)

                            netto_resultaat = 0
                            print(f"[!] Debug: Overall result for number {current_val}: {'WON' if won else 'LOST'}")

                            if won:
                                # We need to calculate the payout per winning chip
                                uitbetaling = 0
                                print(f"[!] Debug: Processing {len(s['current_data']['bets'])} bets for strategy {s['base_copy'].get('title', 'Unknown')}")
                                for bet in s['current_data']['bets']:
                                    # Check if THIS specific square won
                                    original_square = bet['square']
                                    normalized_square = bot.normalize_bet_type(original_square)
                                    bet_won = bot.check_win([bet], current_val)
                                    waarde = sum(float(c['value']) for c in bet['chips'])
                                    print(f"[!] Debug: Bet {original_square} -> {normalized_square} (${waarde:.2f}) - Won: {bet_won}")
                                    if bet_won:
                                        multiplier = bot.get_multiplier(normalized_square) # Use normalized square
                                        # In roulette, multiplier represents TOTAL payout (original bet + winnings)
                                        # Example: $1.60 on dozen (3:1) pays $4.80 total ($1.60 original + $3.20 profit)
                                        win_amount = waarde * multiplier
                                        uitbetaling += win_amount
                                        profit_on_this_bet = win_amount - waarde
                                        print(f"[!] Debug: WIN! Bet ${waarde:.2f} on {normalized_square} -> Total payout ${win_amount:.2f} (profit ${profit_on_this_bet:.2f})")
                                print(f"[!] Debug: Total payout: ${uitbetaling:.2f}, Total bet: ${bet_amount:.2f}")
        
                                netto_resultaat = uitbetaling - bet_amount
                                s['total_win'] += netto_resultaat
                                print(f"[+] TOTAL WIN: ${netto_resultaat:.2f} (Net profit after all bets)")
                                print(f"[!] Summary: Won ${uitbetaling:.2f} - Bet ${bet_amount:.2f} = Net ${netto_resultaat:.2f}")
                            else:
                                netto_resultaat = -bet_amount
                                s['total_loss'] += bet_amount
                                print(f"[-] VERLIES: -${bet_amount:.2f}")
                            
                            # Check conditional triggers
                            bot.check_conditional_triggers(s, won)
                                
                            # Check stop conditions
                            bot.check_stop_conditions(s)
                            
                            # Add to total round profit
                            total_round_profit += netto_resultaat
                            print(f"[!] Debug: Strategy {s['base_copy'].get('title', 'Unknown')} bet ${bet_amount:.2f}, result ${netto_resultaat:.2f}")
                        else:
                            print("[!] Debug: No active strategy found!")
                        
                        print(f"[!] Debug: Final total_round_profit=${total_round_profit:.2f}")
                        # Update the central tracker for the graph with combined profit/loss
                        bot.track_profit_loss(total_round_profit)
                        print(f"[!] Round total profit/loss: ${total_round_profit:.2f}")
                    
                    if not bot.stop_bot and bot.execute_combined_bets():
                        print(f"[!] Bets placed. SPINNING!")
                        bot.hc.move((sx, sy), 0.5)
                        pyautogui.click()
                        
                        bot.first_run_done = True
                        bot.knop_was_weg = False
                        last_val = current_val
                        time.sleep(4)
                    else:
                        print("[X] ERROR: Could not place bets.")
                else:
                    print("[?] Cannot read number.")
        
        time.sleep(0.5)
    
    print("[!] Bot stopped. Goodbye!")
