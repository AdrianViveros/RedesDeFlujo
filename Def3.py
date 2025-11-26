import tkinter as tk
from tkinter import messagebox, simpledialog, scrolledtext, filedialog, ttk
import math
import os
import json 
import subprocess
import tempfile
from collections import deque

try:
    from PIL import Image, ImageDraw, ImageFont
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

class NetworkEditor:
    def __init__(self, root):
        self.root = root
        self.root.title("Editor de Redes")
        self.root.geometry("1280x900")

        # --- Estado del Grafo ---
        self.nodes = []
        self.edges = []
        self.node_counter = 1
        self.source_node_id = None
        self.sink_node_id = None
        
        # --- Variables para Arrastrar Nodos ---
        self.drag_data = {"item": None, "x": 0, "y": 0, "node": None}

        # --- Estado del Algoritmo ---
        self.is_animating = False
        self.current_step = 0
        self.total_max_flow = 0
        self.found_routes = [] 
        self.save_folder = None 
        self.selected_algorithm = "GREEDY"  # Algoritmo por defecto

        self.setup_ui()

    def setup_ui(self):
        # --- BARRA DE HERRAMIENTAS ---
        tools_frame = tk.Frame(self.root, bg="#2C3E50", height=70)
        tools_frame.pack(side=tk.TOP, fill=tk.X)

        # Sección Archivo
        file_frame = tk.Frame(tools_frame, bg="#2C3E50")
        file_frame.pack(side=tk.LEFT, padx=10)
        tk.Label(file_frame, text="Proyecto:", bg="#2C3E50", fg="#BDC3C7", font=("Arial", 8)).pack(side=tk.TOP, anchor="w")
        
        tk.Button(file_frame, text="💾 Guardar", bg="#07a3db", fg="white", width=8,
                 font=("Arial", 9), command=self.save_project_json).pack(side=tk.LEFT, padx=1)
        tk.Button(file_frame, text="📂 Cargar", bg="#7a7200", fg="white", width=8,
                 font=("Arial", 9), command=self.load_project_json).pack(side=tk.LEFT, padx=1)

        
        tk.Frame(tools_frame, width=2, height=40, bg="#34495E").pack(side=tk.LEFT, padx=10, pady=10)

        # Sección Herramientas
        mode_frame = tk.Frame(tools_frame, bg="#2C3E50")
        mode_frame.pack(side=tk.LEFT)
        tk.Label(mode_frame, text="Herramientas:", bg="#2C3E50", fg="#BDC3C7", font=("Arial", 8)).pack(side=tk.TOP, anchor="w")
        
        self.mode_var = tk.StringVar(value="NODE")
        # Usamos botones en lugar de radiobuttons para un look más moderno
        self.btn_node = tk.Button(mode_frame, text="📍 Nodos / Mover", command=lambda: self.set_mode("NODE"), 
                                 bg="#3498DB", fg="white", relief=tk.SUNKEN)
        self.btn_node.pack(side=tk.LEFT, padx=2)
        
        self.btn_edge = tk.Button(mode_frame, text="↗ Arcos", command=lambda: self.set_mode("EDGE"), 
                                 bg="#2C3E50", fg="white", relief=tk.RAISED)
        self.btn_edge.pack(side=tk.LEFT, padx=2)

        # Separador
        tk.Frame(tools_frame, width=2, height=40, bg="#34495E").pack(side=tk.LEFT, padx=10, pady=10)

        # Sección Algoritmos
        algo_frame = tk.Frame(tools_frame, bg="#2C3E50")
        algo_frame.pack(side=tk.LEFT, padx=10)
        tk.Label(algo_frame, text="Algoritmo:", bg="#2C3E50", fg="#BDC3C7", font=("Arial", 8)).pack(side=tk.TOP, anchor="w")
        
        # Combobox para seleccionar algoritmo
        self.algo_var = tk.StringVar(value="GREEDY")
        algo_combo = ttk.Combobox(algo_frame, textvariable=self.algo_var, 
                                 values=["GREEDY", "FORD_FULKERSON_DFS", "EDMONDS_KARP_BFS"], 
                                 state="readonly", width=18)
        algo_combo.pack(side=tk.LEFT, padx=2)
        algo_combo.bind('<<ComboboxSelected>>', self.on_algorithm_change)

        # Separador
        tk.Frame(tools_frame, width=2, height=40, bg="#34495E").pack(side=tk.LEFT, padx=10, pady=10)

        # Sección Ejecución
        run_frame = tk.Frame(tools_frame, bg="#2C3E50")
        run_frame.pack(side=tk.RIGHT, padx=10)
        
        # BOTÓN SEPARADO PARA EJECUTAR
        tk.Button(run_frame, text="EJECUTAR", bg="#27AE60", fg="white", height=2,
                 font=("Arial", 10, "bold"), command=self.start_algorithm).pack(side=tk.LEFT, padx=2)
        
        # BOTÓN SEPARADO PARA GUARDAR FOTOS
        tk.Button(run_frame, text="GUARDAR FOTOS", bg="#3498DB", fg="white", height=2,
                 font=("Arial", 10, "bold"), command=self.start_algorithm_with_photos).pack(side=tk.LEFT, padx=2)
        
        # NUEVO BOTÓN PARA GLPK
        tk.Button(run_frame, text="RESOLVER CON GLPK", bg="#E67E22", fg="white", height=2,
                 font=("Arial", 9, "bold"), command=self.solve_with_glpk).pack(side=tk.LEFT, padx=2)
        
        tk.Button(run_frame, text="Ver Cuellos de Botella", bg="#8E44AD", fg="white", height=2,
                 font=("Arial", 9, "bold"), command=self.highlight_bottlenecks).pack(side=tk.LEFT, padx=2)
        
        tk.Button(run_frame, text="Matriz Incidencia", bg="#16A085", fg="white", height=2,
                 font=("Arial", 9, "bold"), command=self.show_incidence_matrix).pack(side=tk.LEFT, padx=2)
        
        tk.Button(run_frame, text="🗑 Limpiar", bg="#E74C3C", fg="white",
                 font=("Arial", 9), command=self.clear_canvas).pack(side=tk.LEFT, padx=2)

        # --- PANEL PRINCIPAL ---
        main_pane = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, sashrelief=tk.RAISED, sashwidth=6)
        main_pane.pack(fill=tk.BOTH, expand=True)

        # Canvas
        left_frame = tk.Frame(main_pane)
        main_pane.add(left_frame, minsize=800)
        
        self.canvas = tk.Canvas(left_frame, bg="white", bd=2, relief=tk.SUNKEN)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Bindings Mouse
        self.canvas.bind("<Button-1>", self.on_mouse_down)
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_mouse_up)
        self.canvas.bind("<Button-3>", self.on_right_click)

        # Panel Info
        right_frame = tk.Frame(main_pane)
        main_pane.add(right_frame, minsize=350)

        info_frame = tk.LabelFrame(right_frame, text="📊 Estado", font=("Arial", 10, "bold"), padx=10, pady=10)
        info_frame.pack(fill=tk.X, padx=5, pady=5)
        self.info_text = tk.Text(info_frame, height=4, bg="#F8F9FA", font=("Courier New", 9))
        self.info_text.pack(fill=tk.BOTH, expand=True)
        
        log_frame = tk.LabelFrame(right_frame, text="📝 Resultados", font=("Arial", 10, "bold"), padx=10, pady=10)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.log_text = scrolledtext.ScrolledText(log_frame, height=20, bg="#F8F9FA", font=("Courier New", 10))
        self.log_text.pack(fill=tk.BOTH, expand=True)

        self.update_info("Bienvenido. Dibuja tu red o carga un proyecto.")
        self.selected_node = None

    def on_algorithm_change(self, event):
        """Cambia el algoritmo seleccionado"""
        algorithm = self.algo_var.get()
        self.log(f"\n🔧 Algoritmo cambiado a: {algorithm}")
        
        if algorithm == "GREEDY":
            self.log("   - Busca el camino con mayor capacidad disponible en cada paso")
        elif algorithm == "FORD_FULKERSON_DFS":
            self.log("   - Usa DFS para encontrar caminos aumentantes")
        elif algorithm == "EDMONDS_KARP_BFS":
            self.log("   - Usa BFS para encontrar caminos aumentantes (óptimo)")

    # =========================================
    #    NUEVOS ALGORITMOS DE FLUJO MÁXIMO
    # =========================================

    def run_algorithm(self):
        """Ejecuta el algoritmo seleccionado"""
        self.is_animating = True
        algorithm = self.algo_var.get()
        
        if algorithm == "GREEDY":
            self.find_paths_iteratively()
        elif algorithm == "FORD_FULKERSON_DFS":
            self.ford_fulkerson_dfs()
        elif algorithm == "EDMONDS_KARP_BFS":
            self.edmonds_karp_bfs()

    def ford_fulkerson_dfs(self):
        """Implementación de Ford-Fulkerson usando DFS"""
        if not self.is_animating:
            return
            
        # Crear grafo residual
        residual_graph = self.build_residual_graph()
        
        # Encontrar camino aumentante con DFS
        path, min_capacity = self.find_augmenting_path_dfs(residual_graph, self.source_node_id, self.sink_node_id)
        
        if path and min_capacity > 0:
            self.current_step += 1
            self.found_routes.append((path, min_capacity))
            self.highlight_algorithm_step(path)
            self.update_capacities_along_path(path, min_capacity)
            self.total_max_flow += min_capacity
            
            path_str = " → ".join([self.get_node_label(nid) for nid in path])
            self.log(f"\n[Paso {self.current_step}] Camino aumentante (DFS):\n {path_str}")
            self.log(f" Flujo enviado: {min_capacity}")
            
            if self.save_folder:
                filename = os.path.join(self.save_folder, f"{self.current_step:02d}_DFS_Ruta_{min_capacity}.png")
                self.create_snapshot(filename, highlight_path=path)
            
            # Continuar recursivamente
            self.root.after(1200, self.ford_fulkerson_dfs)
        else:
            self.finalize_algorithm()

    def find_augmenting_path_dfs(self, graph, start, end, path=None, visited=None):
        """Encuentra un camino aumentante usando DFS"""
        if path is None:
            path = []
        if visited is None:
            visited = set()
            
        path = path + [start]
        visited.add(start)
        
        if start == end:
            # Calcular capacidad mínima del camino
            min_capacity = float('inf')
            for i in range(len(path) - 1):
                u, v = path[i], path[i+1]
                min_capacity = min(min_capacity, graph[u][v])
            return path, min_capacity
            
        if start in graph:
            for neighbor, capacity in graph[start].items():
                if capacity > 0 and neighbor not in visited:
                    new_path, new_capacity = self.find_augmenting_path_dfs(graph, neighbor, end, path, visited.copy())
                    if new_path:
                        return new_path, new_capacity
                        
        return None, 0

    def edmonds_karp_bfs(self):
        """Implementación de Edmonds-Karp usando BFS"""
        if not self.is_animating:
            return
            
        # Crear grafo residual
        residual_graph = self.build_residual_graph()
        
        # Encontrar camino aumentante con BFS
        path, min_capacity = self.find_augmenting_path_bfs(residual_graph, self.source_node_id, self.sink_node_id)
        
        if path and min_capacity > 0:
            self.current_step += 1
            self.found_routes.append((path, min_capacity))
            self.highlight_algorithm_step(path)
            self.update_capacities_along_path(path, min_capacity)
            self.total_max_flow += min_capacity
            
            path_str = " → ".join([self.get_node_label(nid) for nid in path])
            self.log(f"\n[Paso {self.current_step}] Camino aumentante (BFS):\n {path_str}")
            self.log(f" Flujo enviado: {min_capacity}")
            
            if self.save_folder:
                filename = os.path.join(self.save_folder, f"{self.current_step:02d}_BFS_Ruta_{min_capacity}.png")
                self.create_snapshot(filename, highlight_path=path)
            
            # Continuar recursivamente
            self.root.after(1200, self.edmonds_karp_bfs)
        else:
            self.finalize_algorithm()

    def find_augmenting_path_bfs(self, graph, start, end):
        """Encuentra un camino aumentante usando BFS"""
        visited = set()
        queue = deque()
        queue.append((start, [start], float('inf')))  # (nodo_actual, camino, capacidad_mínima)
        visited.add(start)
        
        while queue:
            current, path, min_cap = queue.popleft()
            
            if current == end:
                return path, min_cap
                
            if current in graph:
                for neighbor, capacity in graph[current].items():
                    if capacity > 0 and neighbor not in visited:
                        visited.add(neighbor)
                        new_min_cap = min(min_cap, capacity)
                        queue.append((neighbor, path + [neighbor], new_min_cap))
                        
        return None, 0

    def build_residual_graph(self):
        """Construye el grafo residual basado en las capacidades actuales"""
        graph = {}
        
        # Inicializar todos los nodos
        for node in self.nodes:
            graph[node['id']] = {}
        
        # Agregar arcos con capacidades residuales
        for edge in self.edges:
            u, v = edge['u'], edge['v']
            if u not in graph:
                graph[u] = {}
            graph[u][v] = edge['remaining_capacity']
            
        return graph

    # =========================================
    #    MATRIZ DE INCIDENCIA
    # =========================================

    def show_incidence_matrix(self):
        """Muestra la matriz de incidencia y capacidades"""
        if not self.nodes or not self.edges:
            messagebox.showwarning("Error", "No hay nodos o arcos en la red.")
            return
            
        # Crear ventana para mostrar la matriz
        matrix_window = tk.Toplevel(self.root)
        matrix_window.title("Matriz de Incidencia y Capacidades")
        matrix_window.geometry("800x600")
        
        # Frame para la matriz
        matrix_frame = tk.Frame(matrix_window)
        matrix_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Text area para mostrar la matriz
        text_area = scrolledtext.ScrolledText(matrix_frame, wrap=tk.NONE, font=("Courier New", 10))
        text_area.pack(fill=tk.BOTH, expand=True)
        
        # Generar y mostrar la matriz
        matrix_text = self.generate_incidence_matrix()
        text_area.insert(tk.END, matrix_text)
        text_area.config(state=tk.DISABLED)
        
        # Botón para exportar
        export_btn = tk.Button(matrix_frame, text="📋 Exportar Matriz", 
                              command=lambda: self.export_matrix_to_file(matrix_text))
        export_btn.pack(pady=5)

    def generate_incidence_matrix(self):
        """Genera la representación textual de la matriz de incidencia"""
        # Ordenar nodos por ID
        sorted_nodes = sorted(self.nodes, key=lambda x: x['id'])
        sorted_edges = sorted(self.edges, key=lambda x: (x['u'], x['v']))
        
        # Encabezado
        result = "MATRIZ DE INCIDENCIA Y CAPACIDADES\n"
        result += "=" * 80 + "\n\n"
        
        # Información de nodos
        result += "NODOS:\n"
        result += "ID  | Label | Tipo      | Coordenadas\n"
        result += "-" * 40 + "\n"
        for node in sorted_nodes:
            node_type = "Fuente" if node['id'] == self.source_node_id else "Sumidero" if node['id'] == self.sink_node_id else "Intermedio"
            result += f"{node['id']:3} | {node['label']:5} | {node_type:9} | ({node['x']}, {node['y']})\n"
        result += "\n"
        
        # Matriz de incidencia
        result += "MATRIZ DE INCIDENCIA (Nodos × Arcos):\n"
        
        # Encabezado de arcos
        arc_headers = []
        for edge in sorted_edges:
            u_label = self.get_node_label(edge['u'])
            v_label = self.get_node_label(edge['v'])
            arc_headers.append(f"{u_label}→{v_label}")
        
        # Construir matriz
        header = "Nodo\\Arco | " + " | ".join(f"{arc:8}" for arc in arc_headers) + " |"
        result += header + "\n"
        result += "-" * len(header) + "\n"
        
        for node in sorted_nodes:
            row = f"{self.get_node_label(node['id']):10} | "
            for edge in sorted_edges:
                if edge['u'] == node['id']:
                    value = "-1"  # Saliente
                elif edge['v'] == node['id']:
                    value = "1"   # Entrante
                else:
                    value = "0"   # No incidente
                row += f"{value:>8} | "
            result += row + "\n"
        
        result += "\n"
        
        # Tabla de capacidades
        result += "CAPACIDADES DE ARCOS:\n"
        result += "Desde | Hasta | Capacidad | Flujo Actual | Capacidad Residual\n"
        result += "-" * 65 + "\n"
        for edge in sorted_edges:
            u_label = self.get_node_label(edge['u'])
            v_label = self.get_node_label(edge['v'])
            result += f"{u_label:5} | {v_label:5} | {edge['capacity']:9} | {edge['current_flow']:12} | {edge['remaining_capacity']:17}\n"
        
        return result

    def export_matrix_to_file(self, matrix_text):
        """Exporta la matriz a un archivo de texto"""
        file_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Archivos de texto", "*.txt"), ("Todos los archivos", "*.*")],
            title="Guardar matriz de incidencia"
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(matrix_text)
                messagebox.showinfo("Éxito", f"Matriz guardada en:\n{file_path}")
            except Exception as e:
                messagebox.showerror("Error", f"No se pudo guardar: {e}")

    # =========================================
    #    MÉTODOS MODIFICADOS PARA SOPORTAR NUEVOS ALGORITMOS
    # =========================================

    def start_algorithm(self):
        """Inicia el algoritmo seleccionado"""
        if self.source_node_id is None or self.sink_node_id is None:
            messagebox.showwarning("Error", "Define Fuente y Sumidero primero.")
            return
            
        algorithm = self.algo_var.get()
        self.save_folder = None
        self.reset_algorithm()
        
        self.log("\n" + "="*50)
        self.log(f" INICIANDO ALGORITMO: {algorithm}")
        self.log("="*50)
        
        if algorithm == "GREEDY":
            self.log("🔧 Algoritmo Greedy: Selecciona el camino con mayor capacidad en cada paso")
        elif algorithm == "FORD_FULKERSON_DFS":
            self.log("🔧 Ford-Fulkerson (DFS): Usa búsqueda en profundidad")
        elif algorithm == "EDMONDS_KARP_BFS":
            self.log("🔧 Edmonds-Karp (BFS): Usa búsqueda en amplitud (óptimo)")
            
        self.prepare_algorithm()
        self.run_algorithm()

    def start_algorithm_with_photos(self):
        """Inicia el algoritmo seleccionado con captura de fotos"""
        if self.source_node_id is None or self.sink_node_id is None:
            messagebox.showwarning("Error", "Define Fuente y Sumidero primero.")
            return
            
        algorithm = self.algo_var.get()
        
        if PIL_AVAILABLE:
            self.save_folder = filedialog.askdirectory(title="Carpeta para guardar imágenes")
            if not self.save_folder: return 
        else:
            messagebox.showwarning("Advertencia", "PIL no disponible. No se guardarán imágenes.")
            self.save_folder = None
            
        self.reset_algorithm()
        
        self.log("\n" + "="*50)
        self.log(f" INICIANDO ALGORITMO: {algorithm} (CON FOTOS)")
        self.log("="*50)
        
        self.prepare_algorithm()
        self.run_algorithm()

    def prepare_algorithm(self):
        """Prepara el estado inicial para cualquier algoritmo"""
        for edge in self.edges:
            edge['current_flow'] = 0
            edge['remaining_capacity'] = edge['capacity']
            self.update_edge_display(edge)
        self.total_max_flow = 0
        self.current_step = 0
        self.found_routes = []
        if self.save_folder:
            algorithm_name = self.algo_var.get().lower()
            self.create_snapshot(os.path.join(self.save_folder, f"00_{algorithm_name}_inicio.png"), show_initial_only=True)

    # =========================================
    #    MÉTODOS EXISTENTES (sin cambios mayores)
    # =========================================

    def set_mode(self, mode):
        self.mode_var.set(mode)
        self.selected_node = None
        self.canvas.delete("highlight")
        
        # Actualizar estilo visual de los botones
        if mode == "NODE":
            self.btn_node.config(bg="#3498DB", relief=tk.SUNKEN)
            self.btn_edge.config(bg="#2C3E50", relief=tk.RAISED)
        else:
            self.btn_node.config(bg="#2C3E50", relief=tk.RAISED)
            self.btn_edge.config(bg="#3498DB", relief=tk.SUNKEN)

    def on_mouse_down(self, event):
        mode = self.mode_var.get()
        x, y = event.x, event.y
        clicked_node = self.find_node_at(x, y)

        if mode == "NODE":
            if clicked_node:
                # Iniciar Arrastre
                self.drag_data["item"] = clicked_node
                self.drag_data["x"] = x
                self.drag_data["y"] = y
                self.highlight_node(clicked_node, "#F1C40F") # Amarillo al mover
            else:
                # Crear Nodo
                self.add_node(x, y)

        elif mode == "EDGE":
            if clicked_node:
                if self.selected_node is None:
                    self.selected_node = clicked_node
                    self.highlight_node(clicked_node, "#3498DB")
                else:
                    if clicked_node['id'] != self.selected_node['id']:
                        if not any(e['u'] == self.selected_node['id'] and e['v'] == clicked_node['id'] for e in self.edges):
                            self.add_edge(self.selected_node, clicked_node)
                    self.selected_node = None
                    self.canvas.delete("highlight")

    def on_mouse_drag(self, event):
        if self.mode_var.get() == "NODE" and self.drag_data["item"]:
            node = self.drag_data["item"]
            dx = event.x - self.drag_data["x"]
            dy = event.y - self.drag_data["y"]
            node['x'] += dx
            node['y'] += dy
            self.canvas.move(node['canvas_ids'][0], dx, dy)
            self.canvas.move(node['canvas_ids'][1], dx, dy)
            self.drag_data["x"] = event.x
            self.drag_data["y"] = event.y
            self.redraw_connected_edges(node)

    def on_mouse_up(self, event):
        self.drag_data["item"] = None
        self.canvas.delete("highlight")

    def redraw_connected_edges(self, node):
        node_id = node['id']
        for edge in self.edges:
            if edge['u'] == node_id or edge['v'] == node_id:
                u = next(n for n in self.nodes if n['id'] == edge['u'])
                v = next(n for n in self.nodes if n['id'] == edge['v'])
                coords = self.get_arrow_coords(u, v)
                self.canvas.coords(edge['canvas_id'], coords['start'][0], coords['start'][1], coords['end'][0], coords['end'][1])
                self.update_edge_text_position(edge, coords)

    def update_info(self, message):
        self.info_text.delete('1.0', tk.END)
        self.info_text.insert(tk.END, message)

    def log(self, message):
        self.log_text.insert(tk.END, message + "\n")
        self.log_text.see(tk.END)

    def get_node_label(self, node_id):
        for node in self.nodes:
            if node['id'] == node_id: return node['label']
        return str(node_id)

    def on_right_click(self, event):
        clicked_node = self.find_node_at(event.x, event.y)
        clicked_edge = self.find_edge_at(event.x, event.y)

        if clicked_node:
            menu = tk.Menu(self.root, tearoff=0)
            menu.add_command(label="✎ Renombrar", command=lambda: self.rename_node(clicked_node))
            menu.add_separator()
            menu.add_command(label="Definir FUENTE", command=lambda: self.set_node_type(clicked_node, 'source'))
            menu.add_command(label="Definir SUMIDERO", command=lambda: self.set_node_type(clicked_node, 'sink'))
            menu.add_separator()
            menu.add_command(label="Eliminar Nodo", command=lambda: self.delete_node(clicked_node))
            menu.post(event.x_root, event.y_root)
        elif clicked_edge:
            menu = tk.Menu(self.root, tearoff=0)
            menu.add_command(label="Cambiar Capacidad", command=lambda: self.change_edge_capacity(clicked_edge))
            menu.add_command(label="Eliminar Arco", command=lambda: self.delete_edge(clicked_edge))
            menu.post(event.x_root, event.y_root)

    def add_node(self, x, y, forced_id=None, forced_label=None, forced_type='transship'):
        node_id = forced_id if forced_id else self.node_counter
        if not forced_id: self.node_counter += 1
        label = forced_label if forced_label else str(node_id)
        
        r = 20
        fill_c = "#ECF0F1"
        if forced_type == 'source': fill_c = "#27AE60"
        if forced_type == 'sink': fill_c = "#E74C3C"

        oval_id = self.canvas.create_oval(x-r, y-r, x+r, y+r, fill=fill_c, outline="#2C3E50", width=2, tags=f"node_{node_id}")
        text_id = self.canvas.create_text(x, y, text=label, font=("Arial", 12, "bold"), tags=f"node_{node_id}")
        
        new_node = {'id': node_id, 'label': label, 'x': x, 'y': y, 'canvas_ids': (oval_id, text_id), 'type': forced_type}
        self.nodes.append(new_node)
        
        if forced_type == 'source': self.source_node_id = node_id
        if forced_type == 'sink': self.sink_node_id = node_id

    def add_edge(self, u_node, v_node, capacity=None):
        if capacity is None:
            capacity = simpledialog.askinteger("Capacidad", f"Capacidad {u_node['label']} → {v_node['label']}:", minvalue=1, initialvalue=5)
        
        if capacity is not None:
            coords = self.get_arrow_coords(u_node, v_node)
            line_id = self.canvas.create_line(coords['start'], coords['end'], arrow=tk.LAST, width=3, fill="#2980B9", tags="edge")
            
            text_x = coords['mid_x'] + coords['off_x']
            text_y = coords['mid_y'] + coords['off_y']
            
            bg_padding = 5
            bg_id = self.canvas.create_rectangle(0, 0, 0, 0, fill="white", outline="#2C3E50", width=1, tags="edge_bg")
            text_id = self.canvas.create_text(text_x, text_y, text=str(capacity), 
                                            fill="#2C3E50", font=("Arial", 10, "bold"), tags="edge_text")
            self.update_edge_background(bg_id, text_id, bg_padding)
            
            self.edges.append({
                'u': u_node['id'], 
                'v': v_node['id'], 
                'capacity': capacity, 
                'current_flow': 0, 
                'remaining_capacity': capacity, 
                'canvas_id': line_id, 
                'text_id': text_id,
                'bg_id': bg_id
            })

    def update_edge_background(self, bg_id, text_id, padding=5):
        bbox = self.canvas.bbox(text_id)
        if bbox:
            x1, y1, x2, y2 = bbox
            self.canvas.coords(bg_id, x1 - padding, y1 - padding, x2 + padding, y2 + padding)
            self.canvas.tag_lower(bg_id, text_id)

    def update_edge_text_position(self, edge, coords):
        text_x = coords['mid_x'] + coords['off_x']
        text_y = coords['mid_y'] + coords['off_y']
        self.canvas.coords(edge['text_id'], text_x, text_y)
        self.update_edge_background(edge['bg_id'], edge['text_id'])

    def get_arrow_coords(self, u, v):
        angle = math.atan2(v['y'] - u['y'], v['x'] - u['x'])
        r = 20
        text_offset = 20
        return {
            'start': (u['x'] + r * math.cos(angle), u['y'] + r * math.sin(angle)),
            'end': (v['x'] - r * math.cos(angle), v['y'] - r * math.sin(angle)),
            'mid_x': (u['x'] + v['x']) / 2,
            'mid_y': (u['y'] + v['y']) / 2,
            'off_x': -text_offset * math.sin(angle),
            'off_y': text_offset * math.cos(angle)
        }

    def find_node_at(self, x, y):
        for n in self.nodes:
            if math.hypot(n['x'] - x, n['y'] - y) <= 25: return n
        return None

    def find_edge_at(self, x, y):
        for e in self.edges:
            coords = self.canvas.coords(e['text_id'])
            if len(coords) == 2 and math.hypot(coords[0] - x, coords[1] - y) <= 20: return e
        return None
    
    def rename_node(self, node):
        new_label = simpledialog.askstring("Renombrar", f"Nombre:", initialvalue=node['label'])
        if new_label:
            node['label'] = new_label
            self.canvas.itemconfig(node['canvas_ids'][1], text=new_label)

    def change_edge_capacity(self, edge):
        new_c = simpledialog.askinteger("Capacidad", "Valor:", initialvalue=edge['capacity'])
        if new_c:
            edge['capacity'] = new_c
            edge['remaining_capacity'] = new_c - edge['current_flow']
            self.update_edge_display(edge)

    def update_edge_display(self, edge):
        if edge['current_flow'] == 0:
            txt = str(edge['capacity'])
        else:
            txt = f"{edge['current_flow']}/{edge['capacity']}"
            if edge['remaining_capacity'] < edge['capacity']: 
                txt += f" ({edge['remaining_capacity']})"
        self.canvas.itemconfig(edge['text_id'], text=txt)
        self.update_edge_background(edge['bg_id'], edge['text_id'])

    def highlight_node(self, node, color):
        self.canvas.delete("highlight")
        self.canvas.create_oval(node['x']-25, node['y']-25, node['x']+25, node['y']+25, outline=color, width=3, tags="highlight")

    def set_node_type(self, node, n_type):
        if n_type == 'source': self.source_node_id = node['id']
        elif n_type == 'sink': self.sink_node_id = node['id']
        node['type'] = n_type
        for n in self.nodes:
            col = "#ECF0F1"
            if n['id'] == self.source_node_id: col = "#27AE60"
            elif n['id'] == self.sink_node_id: col = "#E74C3C"
            self.canvas.itemconfig(n['canvas_ids'][0], fill=col)

    def delete_node(self, node):
        nid = node['id']
        edges_to_remove = [e for e in self.edges if e['u'] == nid or e['v'] == nid]
        for edge in edges_to_remove:
            self.canvas.delete(edge['canvas_id'])
            self.canvas.delete(edge['text_id'])
            self.canvas.delete(edge['bg_id'])
            self.edges.remove(edge)
        if self.source_node_id == nid: self.source_node_id = None
        if self.sink_node_id == nid: self.sink_node_id = None
        self.nodes.remove(node)
        self.canvas.delete(f"node_{nid}")

    def delete_edge(self, edge):
        self.canvas.delete(edge['canvas_id'])
        self.canvas.delete(edge['text_id'])
        self.canvas.delete(edge['bg_id'])
        self.edges.remove(edge)

    def clear_canvas(self):
        self.canvas.delete("all")
        self.nodes = []
        self.edges = []
        self.node_counter = 1
        self.source_node_id = None
        self.sink_node_id = None
        self.reset_algorithm()
        self.log_text.delete('1.0', tk.END)

    def save_project_json(self):
        if not self.nodes:
            messagebox.showwarning("Vacío", "No hay nada que guardar.")
            return
        file_path = filedialog.asksaveasfilename(defaultextension=".json", 
                                               filetypes=[("Archivos JSON", "*.json")])
        if not file_path: return
        data = {
            "node_counter": self.node_counter,
            "source_id": self.source_node_id,
            "sink_id": self.sink_node_id,
            "nodes": [{"id": n['id'], "label": n['label'], "x": n['x'], "y": n['y'], "type": n['type']} for n in self.nodes],
            "edges": [{"u": e['u'], "v": e['v'], "capacity": e['capacity']} for e in self.edges]
        }
        try:
            with open(file_path, 'w') as f:
                json.dump(data, f, indent=4)
            messagebox.showinfo("Guardado", "Proyecto guardado exitosamente.")
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo guardar: {e}")

    def load_project_json(self):
        file_path = filedialog.askopenfilename(filetypes=[("Archivos JSON", "*.json")])
        if not file_path: return
        try:
            with open(file_path, 'r') as f:
                data = json.load(f)
            self.clear_canvas()
            self.node_counter = data.get("node_counter", 1)
            for n_data in data["nodes"]:
                self.add_node(n_data['x'], n_data['y'], 
                             forced_id=n_data['id'], 
                             forced_label=n_data['label'], 
                             forced_type=n_data['type'])
            for e_data in data["edges"]:
                u = next((n for n in self.nodes if n['id'] == e_data['u']), None)
                v = next((n for n in self.nodes if n['id'] == e_data['v']), None)
                if u and v:
                    self.add_edge(u, v, capacity=e_data['capacity'])
            self.source_node_id = data.get("source_id")
            self.sink_node_id = data.get("sink_id")
            messagebox.showinfo("Cargado", "Proyecto cargado correctamente.")
        except Exception as e:
            messagebox.showerror("Error", f"Archivo corrupto o inválido: {e}")

    def find_paths_iteratively(self):
        """Algoritmo Greedy original (para mantener compatibilidad)"""
        if not self.is_animating: return
        path_ids, bottleneck = self.find_path_with_max_capacity()
        if path_ids:
            self.current_step += 1
            self.found_routes.append((path_ids, bottleneck))
            self.highlight_algorithm_step(path_ids)
            self.update_capacities_along_path(path_ids, bottleneck)
            self.total_max_flow += bottleneck
            path_str = " → ".join([self.get_node_label(nid) for nid in path_ids])
            self.log(f"\n[Paso {self.current_step}] Ruta encontrada:\n {path_str}")
            self.log(f" Flujo enviado: {bottleneck}")
            if self.save_folder:
                filename = os.path.join(self.save_folder, f"{self.current_step:02d}_Iteracion_Ruta_{bottleneck}.png")
                self.create_snapshot(filename, highlight_path=path_ids)
            self.root.after(1200, self.find_paths_iteratively)
        else:
            self.finalize_algorithm()

    def find_path_with_max_capacity(self):
        visited = set()
        def dfs(curr, path, flow):
            if curr == self.sink_node_id: return path, flow
            visited.add(curr)
            candidates = []
            for edge in self.edges:
                if edge['u'] == curr and edge['v'] not in visited:
                    if edge['remaining_capacity'] > 0:
                        candidates.append((edge['v'], edge['remaining_capacity']))
            candidates.sort(key=lambda x: x[1], reverse=True)
            for node_v, cap in candidates:
                new_flow = min(flow, cap)
                res_path, res_flow = dfs(node_v, path + [node_v], new_flow)
                if res_path: return res_path, res_flow
            return None, 0
        return dfs(self.source_node_id, [self.source_node_id], float('inf'))

    def update_capacities_along_path(self, path, flow):
        for i in range(len(path)-1):
            u, v = path[i], path[i+1]
            edge = next(e for e in self.edges if e['u']==u and e['v']==v)
            edge['remaining_capacity'] -= flow
            edge['current_flow'] += flow
            self.update_edge_display(edge)

    def highlight_algorithm_step(self, path):
        self.canvas.delete("algorithm_highlight")
        for i in range(len(path)-1):
            u, v = path[i], path[i+1]
            edge = next(e for e in self.edges if e['u']==u and e['v']==v)
            c = self.canvas.coords(edge['canvas_id'])
            if c: self.canvas.create_line(c, width=5, fill="#E67E22", arrow=tk.LAST, tags="algorithm_highlight")

    def finalize_algorithm(self):
        algorithm = self.algo_var.get()
        self.log("\n" + "="*50)
        self.log(f" RESULTADOS FINALES - {algorithm}")
        self.log("="*50)
        
        for i, (p_ids, flow) in enumerate(self.found_routes, 1):
            p_lbls = [self.get_node_label(nid) for nid in p_ids]
            self.log(f"Ruta {i} : {' → '.join(p_lbls)} = {flow}")
        self.log("-" * 40)
        self.log(f"FLUJO MÁXIMO TOTAL: {self.total_max_flow}")
        
        # Información adicional según el algoritmo
        if algorithm == "GREEDY":
            self.log("\n💡 El algoritmo Greedy no siempre encuentra el óptimo global")
        elif algorithm == "FORD_FULKERSON_DFS":
            self.log("\n💡 Ford-Fulkerson con DFS puede ser lento en algunos casos")
        elif algorithm == "EDMONDS_KARP_BFS":
            self.log("\n💡 Edmonds-Karp (BFS) garantiza el óptimo en tiempo polinomial")
            
        self.is_animating = False
        if self.save_folder: 
            messagebox.showinfo("Fin", f"Imágenes guardadas en:\n{self.save_folder}")
        else:
            messagebox.showinfo("Fin", f"Algoritmo completado.\nFlujo máximo: {self.total_max_flow}")

    def highlight_bottlenecks(self):
        if self.total_max_flow == 0:
            messagebox.showinfo("Aviso", "Ejecuta el algoritmo primero.")
            return
        reachable = set()
        stack = [self.source_node_id]
        reachable.add(self.source_node_id)
        while stack:
            u = stack.pop()
            for edge in self.edges:
                if edge['u'] == u and edge['v'] not in reachable and edge['remaining_capacity'] > 0:
                    reachable.add(edge['v'])
                    stack.append(edge['v'])
        min_cut_edges = []
        capacity_sum = 0
        self.canvas.delete("bottleneck_highlight")
        self.log("\n" + "="*50)
        self.log(" ANÁLISIS DE CORTE MÍNIMO (CUELLOS DE BOTELLA)")
        self.log("="*50)
        for edge in self.edges:
            if edge['u'] in reachable and edge['v'] not in reachable:
                min_cut_edges.append(edge)
                capacity_sum += edge['capacity']
                coords = self.canvas.coords(edge['canvas_id'])
                if coords:
                    self.canvas.create_line(coords, width=7, fill="#9B59B6", 
                                          dash=(10, 5), tags="bottleneck_highlight")
                u_lbl = self.get_node_label(edge['u'])
                v_lbl = self.get_node_label(edge['v'])
                self.log(f" 🔒 CUELLO DE BOTELLA: {u_lbl} → {v_lbl} (Cap: {edge['capacity']})")
        self.log(f"\n Capacidad del Corte: {capacity_sum}")
        self.log(f" Flujo Máximo: {self.total_max_flow}")
        if capacity_sum == self.total_max_flow:
            self.log(" ✅ TEOREMA VERIFICADO: Flujo Máx == Corte Mín")
            messagebox.showinfo("Teorema Verificado", f"El algoritmo es correcto.\nSuma de cuellos de botella: {capacity_sum}\nFlujo Total: {self.total_max_flow}")
        else:
            algorithm = self.algo_var.get()
            if algorithm == "GREEDY":
                self.log(" ⚠️ El algoritmo Greedy no siempre garantiza el óptimo global")
            else:
                self.log(" ⚠️ Puede haber un error en la implementación")

    def reset_algorithm(self):
        self.is_animating = False
        self.current_step = 0
        self.total_max_flow = 0
        self.found_routes = []
        self.canvas.delete("algorithm_highlight")
        for edge in self.edges:
            edge['current_flow'] = 0
            edge['remaining_capacity'] = edge['capacity']
            self.update_edge_display(edge)

    def create_snapshot(self, filepath, highlight_path=None, show_initial_only=False):
        if not PIL_AVAILABLE or not self.nodes: return
        scale = 4 
        margin = 100
        max_x = max(n['x'] for n in self.nodes) + margin
        max_y = max(n['y'] for n in self.nodes) + margin
        img = Image.new("RGB", (int(max_x * scale), int(max_y * scale)), "white")
        draw = ImageDraw.Draw(img)
        try:
            font = ImageFont.truetype("arial.ttf", 12 * scale)
            font_bold = ImageFont.truetype("arialbd.ttf", 12 * scale)
        except: font = font_bold = ImageFont.load_default()
        for edge in self.edges:
            u = next(n for n in self.nodes if n['id'] == edge['u'])
            v = next(n for n in self.nodes if n['id'] == edge['v'])
            is_hl = False
            if highlight_path:
                for k in range(len(highlight_path)-1):
                    if highlight_path[k] == edge['u'] and highlight_path[k+1] == edge['v']: is_hl = True; break
            l_col = "#E67E22" if is_hl else "#2980B9"
            l_wid = 6 * scale if is_hl else 3 * scale
            sx, sy, ex, ey = u['x']*scale, u['y']*scale, v['x']*scale, v['y']*scale
            ang = math.atan2(ey - sy, ex - sx)
            r = 20 * scale
            sp = (sx + r * math.cos(ang), sy + r * math.sin(ang))
            ep = (ex - r * math.cos(ang), ey - r * math.sin(ang))
            draw.line([sp, ep], fill=l_col, width=l_wid)
            al, aa = 15 * scale, math.pi / 6
            p1 = (ep[0] - al * math.cos(ang - aa), ep[1] - al * math.sin(ang - aa))
            p2 = (ep[0] - al * math.cos(ang + aa), ep[1] - al * math.sin(ang + aa))
            draw.polygon([ep, p1, p2], fill=l_col)
            mx, my = (sp[0]+ep[0])/2, (sp[1]+ep[1])/2
            ox, oy = -20*scale*math.sin(ang), 20*scale*math.cos(ang)
            txt = str(edge['capacity']) if show_initial_only else f"{edge['current_flow']}/{edge['capacity']}"
            if not show_initial_only and edge['remaining_capacity'] < edge['capacity']: 
                txt += f" ({edge['remaining_capacity']})"
            bbox = draw.textbbox((0, 0), txt, font=font_bold)
            text_width = bbox[2] - bbox[0]
            text_height = bbox[3] - bbox[1]
            padding = 8 * scale
            bg_x1 = mx + ox - text_width/2 - padding
            bg_y1 = my + oy - text_height/2 - padding
            bg_x2 = mx + ox + text_width/2 + padding
            bg_y2 = my + oy + text_height/2 + padding
            draw.rectangle([bg_x1, bg_y1, bg_x2, bg_y2], fill="white", outline="#2C3E50", width=2*scale)
            draw.text((mx+ox, my+oy), txt, fill="black", font=font_bold, anchor="mm")
        for node in self.nodes:
            nx, ny = node['x']*scale, node['y']*scale
            r = 20 * scale
            fill = "#27AE60" if node['id']==self.source_node_id else "#E74C3C" if node['id']==self.sink_node_id else "#ECF0F1"
            out = "#E67E22" if highlight_path and node['id'] in highlight_path else "#2C3E50"
            wid = 5*scale if highlight_path and node['id'] in highlight_path else 3*scale
            draw.ellipse([nx-r, ny-r, nx+r, ny+r], fill=fill, outline=out, width=wid)
            t_col = "white" if node['type'] != 'transship' else "black"
            draw.text((nx, ny), str(node['label']), fill=t_col, font=font_bold, anchor="mm")
        try:
            bbox = img.getbbox()
            if bbox: img = img.crop((bbox[0]-50, bbox[1]-50, bbox[2]+50, bbox[3]+50))
            img.save(filepath, quality=95)
        except: pass

    # =========================================
    #    FUNCIONALIDAD GLPK (sin cambios)
    # =========================================

    def solve_with_glpk(self):
        """Exporta y resuelve el problema con GLPK"""
        if self.source_node_id is None or self.sink_node_id is None:
            messagebox.showwarning("Error", "Define Fuente y Sumidero primero.")
            return
        
        if not self.edges:
            messagebox.showwarning("Error", "No hay arcos en la red.")
            return

        # Primero verificar si GLPK está instalado
        if not self.is_glpk_available():
            self.show_glpk_installation_help()
            return

        # Crear archivo .mod para GLPK
        mod_content = self.generate_glpk_model()
        
        # Preguntar donde guardar
        file_path = filedialog.asksaveasfilename(
            defaultextension=".mod",
            filetypes=[("GLPK Model Files", "*.mod"), ("All files", "*.*")],
            title="Guardar modelo GLPK"
        )
        
        if not file_path:
            return
        
        try:
            # Guardar archivo .mod
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(mod_content)
            
            self.log("\n" + "="*50)
            self.log(" RESOLVIENDO CON GLPK")
            self.log("="*50)
            self.log(f"Archivo guardado: {file_path}")
            
            # Intentar resolver con GLPK
            result = self.run_glpk_solver(file_path)
            
            if result:
                self.log("✅ Solución óptima encontrada con GLPK")
                self.log(f"📊 Flujo máximo (GLPK): {result['max_flow']}")
                self.log("\n🔍 Comparación:")
                self.log(f"   Nuestro algoritmo: {self.total_max_flow}")
                self.log(f"   GLPK (óptimo):     {result['max_flow']}")
                
                if abs(self.total_max_flow - result['max_flow']) < 1e-6:
                    self.log("✅ ¡Nuestro algoritmo encontró el óptimo!")
                else:
                    self.log("⚠️  Nuestro algoritmo no encontró el óptimo")
                    algorithm = self.algo_var.get()
                    if algorithm == "GREEDY":
                        self.log("   (esto es normal para Greedy, no siempre es óptimo)")
                    else:
                        self.log("   (revisa la implementación del algoritmo)")
                
                # Mostrar flujos por arco
                self.log("\n📈 Flujos por arco (GLPK):")
                for edge_data in result['flows']:
                    u_label = self.get_node_label(edge_data['from'])
                    v_label = self.get_node_label(edge_data['to'])
                    self.log(f"   {u_label} → {v_label}: {edge_data['flow']}/{edge_data['capacity']}")
                    
            else:
                self.log("❌ No se pudo resolver con GLPK")
                self.log("💡 Puedes resolver manualmente con:")
                self.log(f"   glpsol --math \"{file_path}\"")
                
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo generar/resolver: {e}")
            self.log(f"❌ Error: {e}")

    def generate_glpk_model(self):
        """Genera el modelo MathProg para GLPK en el formato correcto"""
        
        # Mapear IDs a índices para GLPK
        node_ids = sorted([node['id'] for node in self.nodes])
        node_to_index = {node_id: i+1 for i, node_id in enumerate(node_ids)}
        
        source_idx = node_to_index[self.source_node_id]
        sink_idx = node_to_index[self.sink_node_id]
        
        # Construir el modelo en el formato correcto
        model = f"""/* --- SECCIÓN DEL MODELO --- */

set NODES;
param source, in NODES;
param sink, in NODES;

/* El set ARCS solo contiene pares (origen, destino) */
set ARCS, within NODES cross NODES;

/* La capacidad es un parámetro indexado por los arcos */
param capacity{{ARCS}};

/* Variables de flujo */
var x{{(i,j) in ARCS}}, >= 0;

/* Función objetivo: maximizar flujo saliente de la fuente */
maximize flujo_max: sum{{(source,j) in ARCS}} x[source,j];

/* Restricciones de conservación de flujo (todo lo que entra sale, excepto en fuente y sumidero) */
s.t. conservacion{{i in NODES diff {{source, sink}}}}:
   sum{{(j,i) in ARCS}} x[j,i] = sum{{(i,j) in ARCS}} x[i,j];

/* Restricciones de capacidad */
s.t. limite_cap{{(i,j) in ARCS}}: x[i,j] <= capacity[i,j];

solve;

/* --- REPORTE DE RESULTADOS --- */
printf "\\n=== SOLUCIÓN ÓPTIMA GLPK ===\\n";
printf "Flujo máximo total: %g\\n\\n", flujo_max;
printf "Detalle de arcos utilizados:\\n";
printf "%-10s %-10s %-10s %-10s\\n", "Desde", "Hasta", "Flujo", "Capacidad";
printf "--------------------------------------------\\n";

/* Iteramos sobre los arcos para imprimir solo los que tienen flujo > 0 */
for {{(i,j) in ARCS: x[i,j] > 0}} {{
    printf "%-10s %-10s %-10g %-10g\\n", i, j, x[i,j], capacity[i,j];
}}

printf "--------------------------------------------\\n";


/* --- SECCIÓN DE DATOS --- */
data;

set NODES :="""
        
        # Agregar nodos
        nodes_str = " ".join(str(node_to_index[node_id]) for node_id in node_ids)
        model += f" {nodes_str};\n\n"
        
        model += f"param source := {source_idx};\n"
        model += f"param sink := {sink_idx};\n\n"
        
        model += "/* Formato: Origen Destino Capacidad */\n"
        model += "param : ARCS : capacity :=\n"
        
        # Agregar arcos
        arcs_lines = []
        for edge in self.edges:
            from_idx = node_to_index[edge['u']]
            to_idx = node_to_index[edge['v']]
            arcs_lines.append(f"  {from_idx} {to_idx} {edge['capacity']}")
        
        model += "\n".join(arcs_lines) + "\n;\n\n"
        
        model += "end;"
        
        return model

    def parse_glpk_output(self, output):
        """Parsea la salida de GLPK para extraer resultados del nuevo formato"""
        lines = output.split('\n')
        max_flow = 0
        flows = []
        
        in_flows_section = False
        
        for line in lines:
            # Buscar flujo máximo en el nuevo formato
            if 'Flujo máximo total:' in line:
                try:
                    parts = line.split(':')
                    if len(parts) > 1:
                        max_flow = float(parts[1].strip())
                except:
                    pass
            
            # Buscar sección de flujos en el nuevo formato
            if 'Detalle de arcos utilizados:' in line:
                in_flows_section = True
                # Saltar las siguientes 3 líneas (encabezados y separador)
                continue
                
            if in_flows_section and line.strip() and '---' not in line and 'Desde' not in line:
                parts = line.split()
                if len(parts) >= 4:
                    try:
                        from_node = int(parts[0])
                        to_node = int(parts[1])
                        flow = float(parts[2])
                        capacity = float(parts[3])
                        
                        if flow > 0:
                            flows.append({
                                'from': from_node,
                                'to': to_node,
                                'flow': flow,
                                'capacity': capacity
                            })
                    except:
                        continue
        
        return {'max_flow': max_flow, 'flows': flows}

    def is_glpk_available(self):
        """Verifica si GLPK está instalado y disponible"""
        try:
            result = subprocess.run(['glpsol', '--version'], 
                                  capture_output=True, text=True, timeout=10)
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError, TimeoutError):
            return False

    def show_glpk_installation_help(self):
        """Muestra ayuda para instalar GLPK"""
        help_text = """
GLPK no está instalado en tu sistema.

Para usar esta funcionalidad:

🪟 WINDOWS:
1. Descarga GLPK de: https://ftp.gnu.org/gnu/glpk/
2. O usa el instalador: https://sourceforge.net/projects/winglpk/
3. Agrega la carpeta de GLPK a tu PATH

🐧 LINUX (Ubuntu/Debian):
sudo apt-get update
sudo apt-get install glpk-utils

🍎 macOS:
brew install glpk

💡 También puedes generar el archivo .mod y resolverlo manualmente.
"""
        
        self.log("\n" + "="*50)
        self.log(" GLPK NO ENCONTRADO")
        self.log("="*50)
        self.log(help_text)
        
        # Preguntar si quiere generar el archivo de todos modos
        if messagebox.askyesno("GLPK no encontrado", 
                              "GLPK no está instalado. ¿Quieres generar el archivo .mod para resolverlo manualmente?"):
            self.export_glpk_model_only()

    def export_glpk_model_only(self):
        """Solo exporta el modelo sin resolver"""
        if self.source_node_id is None or self.sink_node_id is None:
            messagebox.showwarning("Error", "Define Fuente y Sumidero primero.")
            return
        
        mod_content = self.generate_glpk_model()
        
        file_path = filedialog.asksaveasfilename(
            defaultextension=".mod",
            filetypes=[("GLPK Model Files", "*.mod"), ("All files", "*.*")],
            title="Guardar modelo GLPK (resolver manualmente)"
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(mod_content)
                
                self.log(f"\n💾 Modelo guardado: {file_path}")
                self.log("🔧 Para resolver manualmente, ejecuta:")
                self.log(f'   glpsol --math "{file_path}"')
                self.log("   o copia el contenido en: https://online-optimizer.appspot.com/")
                
                messagebox.showinfo("Éxito", 
                                  f"Modelo GLPK guardado en:\n{file_path}\n\n"
                                  f"Para resolver manualmente:\n"
                                  f"glpsol --math \"{file_path}\"")
            except Exception as e:
                messagebox.showerror("Error", f"No se pudo guardar: {e}")

    def run_glpk_solver(self, mod_file):
        """Ejecuta GLPK para resolver el modelo"""
        try:
            # Ejecutar GLPK con timeout
            cmd = ['glpsol', '--math', mod_file]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            
            if result.returncode == 0:
                self.log("✅ GLPK ejecutado correctamente")
                return self.parse_glpk_output(result.stdout)
            else:
                self.log(f"❌ Error ejecutando GLPK (código: {result.returncode})")
                if result.stderr:
                    self.log(f"   Error: {result.stderr.strip()}")
                return None
                
        except subprocess.TimeoutExpired:
            self.log("❌ GLPK tardó demasiado tiempo (timeout)")
            return None
        except Exception as e:
            self.log(f"❌ Error ejecutando GLPK: {e}")
            return None

if __name__ == '__main__':
    root = tk.Tk()
    app = NetworkEditor(root)
    root.mainloop()