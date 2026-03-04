# =============================================================================
# PRICE-BASED BOT - OPERA POR NIVELES DE PRECIO PURO
# =============================================================================
# Bot profesional para operar futuros basándose en PRECIOS directos (sin TNA)
# Optimizado con mejores prácticas de Primary API
# =============================================================================

import os
import sys
import logging
import numpy as np
import pyRofex
import math
from datetime import datetime, timedelta
import time
import signal
import threading
from typing import Dict, List, Optional, Tuple
from dotenv import load_dotenv
import matplotlib.pyplot as plt
from collections import deque
import csv

# =============================================================================
# CONFIGURACIÓN DE LOGGING
# =============================================================================

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    handlers=[
        logging.FileHandler('price_based_bot.log', encoding='utf-8'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

# =============================================================================
# CARGAR VARIABLES DE ENTORNO
# =============================================================================
load_dotenv()  # Cargar credenciales desde archivo .env

# =============================================================================
# CLASE PRINCIPAL DEL BOT
# =============================================================================

class PriceBasedBot:
    """Bot de trading basado en niveles de PRECIO puro"""
    
    def __init__(self, config: Dict):
        self.config = config
        self.future_symbol = config['future_symbol']
        self.tick_size = config['tick_size']
        self.order_quantity = config['order_quantity']
        
        # PARÁMETROS DE ENTRADA BASADOS EN PRECIO
        # =======================================
        self.entry_side = config.get('entry_side', 'BUY')  # BUY o SELL
        
        # Validar entry_side
        if self.entry_side not in ('BUY', 'SELL'):
            raise ValueError(f"entry_side debe ser 'BUY' o 'SELL', recibido: {self.entry_side}")
        
        if self.entry_side == 'BUY':
            # Comprar cuando precio <= precio_max
            self.entry_max_price = config.get('entry_max_price', 1650.0)
            self.entry_min_price = None  # No usado en BUY
        else:  # SELL
            # Vender cuando precio >= precio_min
            self.entry_min_price = config.get('entry_min_price', 1700.0)
            self.entry_max_price = None  # No usado en SELL
        
        # Validar configuración crítica
        if self.tick_size <= 0:
            raise ValueError(f"tick_size debe ser > 0, recibido: {self.tick_size}")
        if self.order_quantity <= 0:
            raise ValueError(f"order_quantity debe ser > 0, recibido: {self.order_quantity}")
        
        # FILTROS
        # =======
        self.filter_market_hours_only = config.get('filter_market_hours_only', True)
        self.filter_max_data_age_seconds = config.get('filter_max_data_age_seconds', 5)
        
        # GATILLO
        # =======
        self.trigger_type = config.get('trigger_type', "IMMEDIATE")
        self.trigger_price_improvement_ticks = config.get('trigger_price_improvement_ticks', 0)
        # Aplicar mejora de precio por defecto en 1 tick (0.5) para quedar primero en el book
        # Si no se especifica, usar 1. Si el usuario pone 0, forzamos 1 para este bot de precio.
        self.improvement_ticks = max(1, int(config.get('improvement_ticks', self.trigger_price_improvement_ticks or 1)))
        
        # TARGET (SALIDA)
        # ===============
        self.target_profit_ticks = config.get('target_profit_ticks', 10)
        self.target_stop_loss_ticks = config.get('target_stop_loss_ticks', 5)
        self.target_time_exit_minutes = config.get('target_time_exit_minutes', 120)
        
        # GESTIÓN DE POSICIÓN BASADA EN TIEMPO (TP DEGRADADO)
        # ====================================================
        self.time_based_tp_enabled = config.get('time_based_tp_enabled', False)
        self.tp_initial_ticks = config.get('tp_initial_ticks', 1.0)  # TP inicial (ej: 1 tick)
        self.tp_degradation_time_minutes = config.get('tp_degradation_time_minutes', 1.0)  # Tiempo para degradar (ej: 1 min)
        self.tp_degraded_ticks = config.get('tp_degraded_ticks', 0.5)  # TP degradado (ej: 0.5 ticks)
        self.tp_break_even_time_minutes = config.get('tp_break_even_time_minutes', 2.0)  # Tiempo para break even (ej: 2 min)
        self.tp_stop_loss_time_minutes = config.get('tp_stop_loss_time_minutes', 3.0)  # Tiempo para aplicar SL (ej: 3 min)
        
        # SALIDAS CON PRECIOS FIJOS (EJECUCIÓN INSTANTÁNEA)
        # ===================================================
        # Lista de precios fijos donde salir automáticamente
        # Formato: [(precio1, cantidad1), (precio2, cantidad2), ...]
        # Si cantidad es None o 0, sale completamente en ese precio
        # Ejemplo: [(1512.0, 1), (1515.0, 2), (1520.0, None)] -> Sale 1 contrato a 1512, 2 a 1515, resto a 1520
        self.fixed_exit_prices = config.get('fixed_exit_prices', [])
        # Control de salidas parciales ya ejecutadas
        self.executed_partial_exits = {}  # {precio: cantidad_ejecutada}
        
        # VALUACIÓN TEÓRICA (opcional)
        # ============================
        self.use_theoretical_valuation = config.get('use_theoretical_valuation', False)
        self.spot_price = config.get('spot_price', None)
        self.risk_free_rate = config.get('risk_free_rate', None)
        self.valuation_model = config.get('valuation_model', 'simple')
        self.domestic_rate = config.get('domestic_rate', None)
        self.foreign_rate = config.get('foreign_rate', None)
        self.use_business_days_for_carry = config.get('use_business_days_for_carry', True)
        self.days_to_expiry_override = config.get('days_to_expiry_override', None)
        self.cheap_threshold_pct = config.get('cheap_threshold_pct', 0.0)
        self.expensive_threshold_pct = config.get('expensive_threshold_pct', 0.0)
        
        # ESTADO DEL BOT
        # ==============
        self.running = False
        self.position_opened = False
        self.entry_price = None
        self.entry_time = None
        self.entry_side_actual = None
        self.position_quantity = 0  # Cantidad de contratos en posición actual
        self.entry_target_quantity = self.order_quantity  # Objetivo de cantidad al abrir posición
        self.allow_entry_topup = False  # Permite completar contratos faltantes tras fills parciales
        self.last_order_time = 0
        self.dynamic_order_interval = 5
        self.last_close_time = 0
        
        # SISTEMA ADAPTATIVO
        # ==================
        self.adaptive_speed = config.get('adaptive_speed', True)
        self.order_timeout_seconds = config.get('order_timeout_seconds', 60)
        
        # CONTROL DE OPERACIONES
        # =======================
        self.max_operations_per_day = config.get('max_operations_per_day', None)  # None = sin límite
        self.max_operations_total = config.get('max_operations_total', None)  # None = sin límite
        self.operations_count_today = 0
        self.operations_count_total = 0
        self.last_operations_reset_date = datetime.now().date()  # Para resetear contador diario
        self.operations_history = []  # Lista de timestamps de operaciones
        
        # TRACKING DE MEJORA DE PRECIO (evitar mejoras constantes)
        # =========================================================
        self.orders_price_improved = set()  # clOrdIds de órdenes que ya fueron mejoradas
        self.allow_price_improvement_once = config.get('allow_price_improvement_once', True)  # Solo mejorar una vez por orden
        
        # DATOS DE MERCADO
        # ================
        self.depth_levels_to_track = max(1, int(config.get('depth_levels_to_track', 5)))
        self.min_depth_contracts = max(0, int(config.get('min_depth_contracts', 0)))
        self.market_data = {
            'bid': None,
            'offer': None,
            'last': None,
            'timestamp': None,
            'bid_size': 0.0,
            'offer_size': 0.0,
            'bid_depth': 0.0,
            'offer_depth': 0.0
        }
        
        # ÓRDENES (MEJORADO CON PRIMARY API)
        # ===================================
        self.active_orders = {}
        self.order_states = {}
        self.active_order = None
        self.proprietary = "api"  # Campo requerido por API
        self.ws_order_counter = 0  # Para wsClOrdId único
        self.order_cancel_pending = set()  # clOrdIds con cancelación solicitada
        self.entry_registered = False
        
        # LOCK para prevenir envío de múltiples órdenes simultáneamente
        self._order_lock = False  # Flag para bloquear envío de nuevas órdenes mientras se procesa una
        self._last_order_send_attempt = 0  # Timestamp del último intento de envío
        
        # TimeInForce y OrderType configurables
        self.time_in_force = config.get('time_in_force', 'DAY')
        self.order_type = config.get('order_type', 'LIMIT')
        
        # CONFIGURACIÓN DE I/O Y TIMEOUTS
        # ===============================
        self.api_timeout_seconds = config.get('api_timeout_seconds', 30)  # Timeout para llamadas REST
        self.websocket_timeout_seconds = config.get('websocket_timeout_seconds', 60)  # Si no hay data por X segundos, reconectar
        self.max_reconnect_attempts = config.get('max_reconnect_attempts', 5)
        self.websocket_reconnect_attempts = 0
        self.last_market_data_time = None  # Para detectar si WebSocket está vivo
        self.websocket_connected = False
        
        # TRACKING DE LATENCIA
        # ====================
        self.latency_history = deque(maxlen=100)
        self.latency_timestamps = deque(maxlen=100)
        self.last_latency = 0.0
        self.latency_warning_threshold = 1.0
        self.alert_throttle_count = 0
        self.optimized_mode = config.get('optimized_mode', False)
        
        # FILTRO DE LATENCIA - CONFIGURABLE
        # ==================================
        # CAMBIAR A False PARA OPERAR INMEDIATAMENTE (sin esperar calibración)
        self.enable_latency_filter = config.get('enable_latency_filter', False)
        self.latency_baseline_ms = None
        self.latency_std_baseline_ms = None
        self.min_samples_for_stability = 20
        self.max_latency_multiplier = 1.0  # Solo operar en/bajo promedio
        self.max_std_multiplier = 2.0
        self.is_latency_calibrated = False
        
        # CALIBRACIÓN INICIAL (5 minutos) - solo si filtro activo
        # ========================================================
        self.calibration_period_seconds = 300 if self.enable_latency_filter else 0
        self.calibration_start_time = None
        self.is_calibration_complete = not self.enable_latency_filter  # Si está desactivado, ya está "completo"
        self.last_calibration_status_time = 0
        self.last_latency_log_time = 0  # Throttle para logs de latencia
        self.latency_log_interval = 30  # Mostrar cada 30 segundos máximo
        
        # CSV LOGGING
        # ===========
        timestamp_str = datetime.now().strftime("%Y%m%d_%H%M%S")
        symbol_clean = self.future_symbol.replace("/", "_")
        self.csv_filename = f'trades_price_{symbol_clean}_{timestamp_str}.csv'
        self.csv_orders_filename = f'orders_price_{symbol_clean}_{timestamp_str}.csv'
        self.csv_latency_filename = f'latency_{symbol_clean}_{timestamp_str}.csv'
        self._init_csv_files()
        
        # GRÁFICO DE LATENCIA EN VIVO
        # ============================
        self.plot_latency_live = config.get('plot_latency_live', False)
        self.latency_plot_fig = None
        self.latency_plot_ax = None
        self.latency_plot_line = None
        self.latency_plot_update_interval = 10  # Actualizar cada 10 segundos para no estorbar
        
        logger.info(f"[OK] Bot inicializado para operar PRECIO PURO: {self.future_symbol}")
        logger.info(f"[INFO] Modo: {self.entry_side}")
        if self.entry_side == 'BUY':
            logger.info(f"[INFO] Comprar cuando precio <= ${self.entry_max_price}")
        else:
            logger.info(f"[INFO] Vender cuando precio >= ${self.entry_min_price}")
        logger.info(f"[INFO] CSV logs:")
        logger.info(f"   - Trades: {self.csv_filename}")
        logger.info(f"   - Ordenes: {self.csv_orders_filename}")
        logger.info(f"   - Latencia: {self.csv_latency_filename}")
        if self.plot_latency_live:
            logger.info(f"   - Gráfico en vivo: ACTIVADO (actualiza cada {self.latency_plot_update_interval}s)")
    
    # =============================================================================
    # CSV LOGGING
    # =============================================================================
    
    def _init_csv_files(self):
        """Inicializa archivos CSV"""
        try:
            with open(self.csv_filename, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'timestamp', 'side', 'entry_price', 'exit_price', 
                    'quantity', 'pnl_ticks', 'pnl_usd', 'pnl_porcentaje',
                    'duracion_min', 'duracion_seg', 'exit_reason', 
                    'latencia_promedio_ms', 'es_ganador'
                ])
            logger.info(f"[OK] CSV de trades creado: {self.csv_filename}")
            
            # CSV de métricas agregadas DESACTIVADO (calcular al final con herramientas externas)
            # No se crea archivo de métricas para evitar redundancia y ahorrar espacio
            self.csv_metrics_filename = None
            
            # Crear CSV de latencia
            with open(self.csv_latency_filename, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow(['timestamp', 'latencia_ms'])
            logger.info(f"[OK] CSV de latencia creado: {self.csv_latency_filename}")
        except Exception as e:
            logger.error(f"[ERROR] No se pudo crear CSV de trades: {e}")
        
        try:
            with open(self.csv_orders_filename, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    'timestamp', 'order_id', 'side', 'price', 'quantity',
                    'status', 'filled_price', 'latencia_ms', 'tipo_gatillo'
                ])
            logger.info(f"[OK] CSV de ordenes creado: {self.csv_orders_filename}")
        except Exception as e:
            logger.error(f"[ERROR] No se pudo crear CSV de ordenes: {e}")
    
    def _log_order_to_csv(self, order_id: str, side: str, price: float, quantity: int, 
                          status: str, filled_price: Optional[float] = None):
        """Registra una orden en CSV - SOLO ESTADOS FINALES"""
        try:
            # OPTIMIZACIÓN: Solo registrar estados finales para reducir ruido
            # Estados intermedios (SENT, PENDING_NEW, NEW) no aportan valor al análisis
            final_states = ['FILLED', 'CANCELLED', 'REJECTED']
            if status not in final_states:
                logger.debug(f"[CSV] Saltando registro de estado intermedio: {status} para {order_id}")
                return
            
            # Validar parámetros
            if not order_id:
                logger.warning("[WARNING] order_id vacío, no se puede registrar en CSV")
                return
            if not isinstance(price, (int, float)) or price is None:
                logger.warning(f"[WARNING] Precio inválido para CSV: {price}")
                price = 0.0  # Usar 0 como fallback
            if not isinstance(quantity, int) or quantity <= 0:
                logger.warning(f"[WARNING] Cantidad inválida para CSV: {quantity}")
                quantity = 0
            
            latencia_ms = (self.last_latency * 1000) if self.last_latency else 0.0
            
            with open(self.csv_orders_filename, 'a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                    str(order_id),
                    str(side) if side else '',
                    f"{float(price):.2f}" if price else '',
                    int(quantity),
                    str(status) if status else '',
                    f"{float(filled_price):.2f}" if filled_price and isinstance(filled_price, (int, float)) else '',
                    f"{latencia_ms:.1f}",
                    str(self.trigger_type) if self.trigger_type else ''
                ])
            logger.debug(f"[CSV] Orden registrada: {order_id} | {status}")
        except Exception as e:
            logger.error(f"[ERROR] No se pudo escribir orden en CSV: {e}")
            import traceback
            logger.error(f"[ERROR] Traceback:\n{traceback.format_exc()}")
    
    def _log_trade_to_csv(self, side: str, entry_price: float, exit_price: float,
                          pnl_ticks: float, duracion_min: float, exit_reason: str,
                          quantity: Optional[int] = None):
        """Registra un trade completo en CSV con métricas mejoradas"""
        try:
            # Validar parámetros antes de calcular
            if not isinstance(entry_price, (int, float)) or entry_price <= 0:
                logger.warning(f"[WARNING] entry_price inválido para CSV: {entry_price}")
                return
            if not isinstance(exit_price, (int, float)) or exit_price <= 0:
                logger.warning(f"[WARNING] exit_price inválido para CSV: {exit_price}")
                return
            if not isinstance(pnl_ticks, (int, float)):
                logger.warning(f"[WARNING] pnl_ticks inválido para CSV: {pnl_ticks}")
                pnl_ticks = 0.0
            if not isinstance(duracion_min, (int, float)) or duracion_min < 0:
                logger.warning(f"[WARNING] duracion_min inválido para CSV: {duracion_min}")
                duracion_min = 0.0
            
            # Validar tick_size y order_quantity antes de calcular pnl_usd
            trade_quantity = quantity if isinstance(quantity, (int, float)) and quantity > 0 else self.order_quantity
            if not self.tick_size or self.tick_size <= 0:
                logger.warning(f"[WARNING] tick_size inválido para calcular P&L USD: {self.tick_size}")
                pnl_usd = 0.0
            elif not self.order_quantity or self.order_quantity <= 0:
                logger.warning(f"[WARNING] order_quantity inválido para calcular P&L USD: {self.order_quantity}")
                pnl_usd = pnl_ticks * self.tick_size * trade_quantity if trade_quantity else 0.0
            else:
                pnl_usd = pnl_ticks * self.tick_size * trade_quantity
            
            # Calcular P&L porcentual
            pnl_porcentaje = ((exit_price - entry_price) / entry_price) * 100.0 if entry_price > 0 else 0.0
            if side == 'SELL':
                pnl_porcentaje = -pnl_porcentaje  # Invertir para SELL
            
            # Duración en segundos
            duracion_seg = duracion_min * 60.0
            
            # Determinar si es ganador
            es_ganador = 'SI' if pnl_ticks > 0 else 'NO' if pnl_ticks < 0 else 'EMPATE'
            
            latencia_promedio = np.mean(list(self.latency_history)) * 1000 if len(self.latency_history) > 0 else 0
            
            with open(self.csv_filename, 'a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                    side,
                    f"{entry_price:.2f}",
                    f"{exit_price:.2f}",
                    int(trade_quantity),
                    f"{pnl_ticks:.2f}",
                    f"{pnl_usd:.2f}",
                    f"{pnl_porcentaje:.2f}",
                    f"{duracion_min:.2f}",
                    f"{duracion_seg:.1f}",
                    exit_reason,
                    f"{latencia_promedio:.1f}",
                    es_ganador
                ])
            logger.info(f"[OK] Trade registrado en CSV: {side} | P&L: {pnl_ticks:+.2f}t (${pnl_usd:+.2f}) | {es_ganador}")
            
            # Métricas agregadas desactivadas (calcular al final con Excel/Python)
            # self._update_metrics_csv()  # DESACTIVADO - genera archivo redundante
        except Exception as e:
            logger.error(f"[ERROR] No se pudo escribir trade en CSV: {e}")
            import traceback
            logger.error(traceback.format_exc())
    
    def _update_metrics_csv(self):
        """Calcula y guarda métricas agregadas en CSV de métricas (sin pandas)"""
        try:
            import os
            
            # Leer CSV de trades si existe
            if not os.path.exists(self.csv_filename):
                return
            
            # Leer CSV manualmente
            trades_data = []
            try:
                with open(self.csv_filename, 'r', encoding='utf-8') as f:
                    reader = csv.DictReader(f)
                    for row in reader:
                        try:
                            trades_data.append({
                                'timestamp': row.get('timestamp', ''),
                                'pnl_ticks': float(row.get('pnl_ticks', 0) or 0),
                                'pnl_usd': float(row.get('pnl_usd', 0) or 0),
                                'duracion_min': float(row.get('duracion_min', 0) or 0),
                                'duracion_seg': float(row.get('duracion_seg', 0) or 0),
                                'quantity': int(float(row.get('quantity', 0) or 0))
                            })
                        except (ValueError, TypeError):
                            continue
            except Exception as e:
                logger.debug(f"[METRICS] No se pudo leer CSV de trades: {e}")
                return
            
            if len(trades_data) == 0:
                return
            
            # Calcular métricas básicas
            total_trades = len(trades_data)
            pnl_ticks_list = [t['pnl_ticks'] for t in trades_data]
            pnl_usd_list = [t['pnl_usd'] for t in trades_data]
            
            trades_ganadores = sum(1 for pnl in pnl_ticks_list if pnl > 0)
            trades_perdedores = sum(1 for pnl in pnl_ticks_list if pnl < 0)
            
            win_rate_pct = (trades_ganadores / total_trades * 100.0) if total_trades > 0 else 0.0
            
            # P&L total
            pnl_total_ticks = sum(pnl_ticks_list)
            pnl_total_usd = sum(pnl_usd_list)
            
            # Esperanza matemática (Expected Value)
            esperanza_matematica_ticks = pnl_total_ticks / total_trades if total_trades > 0 else 0.0
            esperanza_matematica_usd = pnl_total_usd / total_trades if total_trades > 0 else 0.0
            
            # Ganancias y pérdidas
            ganancias_ticks = [pnl for pnl in pnl_ticks_list if pnl > 0]
            perdidas_ticks = [abs(pnl) for pnl in pnl_ticks_list if pnl < 0]
            
            ganancias_usd = [pnl for pnl in pnl_usd_list if pnl > 0]
            perdidas_usd = [abs(pnl) for pnl in pnl_usd_list if pnl < 0]
            
            ganancia_promedio_ticks = sum(ganancias_ticks) / len(ganancias_ticks) if len(ganancias_ticks) > 0 else 0.0
            perdida_promedio_ticks = sum(perdidas_ticks) / len(perdidas_ticks) if len(perdidas_ticks) > 0 else 0.0
            
            ganancia_promedio_usd = sum(ganancias_usd) / len(ganancias_usd) if len(ganancias_usd) > 0 else 0.0
            perdida_promedio_usd = sum(perdidas_usd) / len(perdidas_usd) if len(perdidas_usd) > 0 else 0.0
            
            # Profit Factor
            total_ganancias = sum(ganancias_ticks)
            total_perdidas = sum(perdidas_ticks)
            profit_factor = total_ganancias / total_perdidas if total_perdidas > 0 else float('inf') if total_ganancias > 0 else 0.0
            
            # Ratio ganancia/pérdida promedio
            ratio_ganancia_perdida = ganancia_promedio_ticks / perdida_promedio_ticks if perdida_promedio_ticks > 0 else float('inf') if ganancia_promedio_ticks > 0 else 0.0
            
            # Máximas ganancias y pérdidas
            maxima_ganancia_ticks = max(ganancias_ticks) if len(ganancias_ticks) > 0 else 0.0
            maxima_perdida_ticks = max(perdidas_ticks) if len(perdidas_ticks) > 0 else 0.0
            
            maxima_ganancia_usd = max(ganancias_usd) if len(ganancias_usd) > 0 else 0.0
            maxima_perdida_usd = max(perdidas_usd) if len(perdidas_usd) > 0 else 0.0
            
            # Duración
            duraciones_min = [t['duracion_min'] for t in trades_data]
            duraciones_seg = [t['duracion_seg'] for t in trades_data]
            
            duracion_promedio_min = sum(duraciones_min) / len(duraciones_min) if len(duraciones_min) > 0 else 0.0
            duracion_promedio_seg = sum(duraciones_seg) / len(duraciones_seg) if len(duraciones_seg) > 0 else 0.0
            duracion_minima_min = min(duraciones_min) if len(duraciones_min) > 0 else 0.0
            duracion_maxima_min = max(duraciones_min) if len(duraciones_min) > 0 else 0.0
            
            # Máximo Drawdown
            pnl_acumulado_ticks = 0.0
            pnl_acumulado_usd = 0.0
            running_max_ticks = 0.0
            running_max_usd = 0.0
            max_drawdown_ticks = 0.0
            max_drawdown_usd = 0.0
            
            for i, trade in enumerate(trades_data):
                pnl_acumulado_ticks += trade['pnl_ticks']
                pnl_acumulado_usd += trade['pnl_usd']
                
                running_max_ticks = max(running_max_ticks, pnl_acumulado_ticks)
                running_max_usd = max(running_max_usd, pnl_acumulado_usd)
                
                drawdown_ticks = pnl_acumulado_ticks - running_max_ticks
                drawdown_usd = pnl_acumulado_usd - running_max_usd
                
                max_drawdown_ticks = max(max_drawdown_ticks, abs(drawdown_ticks))
                max_drawdown_usd = max(max_drawdown_usd, abs(drawdown_usd))
            
            # Sharpe Ratio (simplificado: promedio / desviación estándar)
            if len(pnl_ticks_list) > 1:
                mean_pnl = esperanza_matematica_ticks
                variance = sum((pnl - mean_pnl) ** 2 for pnl in pnl_ticks_list) / len(pnl_ticks_list)
                std_pnl_ticks = math.sqrt(variance) if variance > 0 else 0.0
                sharpe_ratio = esperanza_matematica_ticks / std_pnl_ticks if std_pnl_ticks > 0 else 0.0
            else:
                sharpe_ratio = 0.0
            
            # Guardar métricas en CSV
            with open(self.csv_metrics_filename, 'a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                    int(total_trades),
                    int(trades_ganadores),
                    int(trades_perdedores),
                    f"{win_rate_pct:.2f}",
                    f"{pnl_total_ticks:.2f}",
                    f"{pnl_total_usd:.2f}",
                    f"{esperanza_matematica_ticks:.2f}",
                    f"{esperanza_matematica_usd:.2f}",
                    f"{ganancia_promedio_ticks:.2f}",
                    f"{ganancia_promedio_usd:.2f}",
                    f"{perdida_promedio_ticks:.2f}",
                    f"{perdida_promedio_usd:.2f}",
                    f"{profit_factor:.2f}" if profit_factor != float('inf') else "INF",
                    f"{ratio_ganancia_perdida:.2f}" if ratio_ganancia_perdida != float('inf') else "INF",
                    f"{maxima_ganancia_ticks:.2f}",
                    f"{maxima_ganancia_usd:.2f}",
                    f"{maxima_perdida_ticks:.2f}",
                    f"{maxima_perdida_usd:.2f}",
                    f"{duracion_promedio_min:.2f}",
                    f"{duracion_promedio_seg:.1f}",
                    f"{duracion_minima_min:.2f}",
                    f"{duracion_maxima_min:.2f}",
                    f"{max_drawdown_ticks:.2f}",
                    f"{max_drawdown_usd:.2f}",
                    f"{sharpe_ratio:.2f}",
                    f"{pnl_acumulado_ticks:.2f}",
                    f"{pnl_acumulado_usd:.2f}"
                ])
            
            logger.info(f"[METRICS] Métricas actualizadas: {total_trades} trades | Win Rate: {win_rate_pct:.1f}% | P&L: {pnl_total_ticks:+.2f}t (${pnl_total_usd:+.2f})")
            
        except Exception as e:
            logger.error(f"[ERROR] Error calculando métricas: {e}")
            import traceback
            logger.error(traceback.format_exc())
    
    def _log_latency_to_csv(self, latency_ms: float):
        """Guarda medición de latencia en CSV"""
        try:
            with open(self.csv_latency_filename, 'a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')[:-3],  # Con milisegundos
                    f"{latency_ms:.1f}"
                ])
        except Exception as e:
            logger.debug(f"[ERROR] No se pudo escribir latencia en CSV: {e}")
    
    def _update_latency_plot(self):
        """Actualiza gráfico de latencia en vivo (cada 10s para no estorbar)"""
        try:
            # Throttle: solo actualizar cada X segundos
            if not hasattr(self, '_last_plot_update'):
                self._last_plot_update = 0
            
            now = time.time()
            if now - self._last_plot_update < self.latency_plot_update_interval:
                return
            
            self._last_plot_update = now
            
            # Inicializar figura si no existe
            if self.latency_plot_fig is None:
                plt.ion()  # Modo interactivo
                self.latency_plot_fig, self.latency_plot_ax = plt.subplots(figsize=(10, 4))
                self.latency_plot_ax.set_title('Latencia del Mercado (En Vivo)')
                self.latency_plot_ax.set_xlabel('Tiempo')
                self.latency_plot_ax.set_ylabel('Latencia (ms)')
                self.latency_plot_ax.grid(True, alpha=0.3)
            
            # Actualizar datos
            if len(self.latency_history) > 0:
                latencies_ms = [lat * 1000 for lat in self.latency_history]
                timestamps = list(self.latency_timestamps)
                
                self.latency_plot_ax.clear()
                self.latency_plot_ax.plot(timestamps, latencies_ms, 'b-', linewidth=1, alpha=0.7)
                
                # Línea de baseline si está calibrado
                if self.is_latency_calibrated and self.latency_baseline_ms:
                    self.latency_plot_ax.axhline(y=self.latency_baseline_ms, 
                                                  color='r', linestyle='--', 
                                                  label=f'Baseline (P75): {self.latency_baseline_ms:.1f}ms')
                
                self.latency_plot_ax.set_title(f'Latencia del Mercado - {self.future_symbol}')
                self.latency_plot_ax.set_xlabel('Tiempo')
                self.latency_plot_ax.set_ylabel('Latencia (ms)')
                self.latency_plot_ax.grid(True, alpha=0.3)
                self.latency_plot_ax.legend()
                
                plt.pause(0.01)  # Actualizar sin bloquear
        
        except Exception as e:
            logger.debug(f"[ERROR] Error actualizando gráfico de latencia: {e}")
    
    def _save_latency_plot(self):
        """Guarda gráfico final de latencia al detener el bot"""
        try:
            if len(self.latency_history) == 0:
                return
            
            # Crear figura final
            fig, ax = plt.subplots(figsize=(12, 6))
            
            latencies_ms = [lat * 1000 for lat in self.latency_history]
            timestamps = list(self.latency_timestamps)
            
            ax.plot(timestamps, latencies_ms, 'b-', linewidth=1, alpha=0.7, label='Latencia')
            
            # Estadísticas
            mean_lat = np.mean(latencies_ms)
            p75_lat = np.percentile(latencies_ms, 75)
            
            ax.axhline(y=mean_lat, color='g', linestyle='--', label=f'Promedio: {mean_lat:.1f}ms')
            ax.axhline(y=p75_lat, color='r', linestyle='--', label=f'P75 (baseline): {p75_lat:.1f}ms')
            
            ax.set_title(f'Latencia del Mercado - {self.future_symbol}')
            ax.set_xlabel('Tiempo')
            ax.set_ylabel('Latencia (ms)')
            ax.grid(True, alpha=0.3)
            ax.legend()
            
            # Guardar
            filename = f'latency_plot_{self.future_symbol.replace("/", "_")}_{datetime.now().strftime("%Y%m%d_%H%M%S")}.png'
            plt.savefig(filename, dpi=150, bbox_inches='tight')
            logger.info(f"[OK] Gráfico de latencia guardado: {filename}")
            plt.close(fig)
            
        except Exception as e:
            logger.error(f"[ERROR] Error guardando gráfico de latencia: {e}")
    
    def _extract_level_size(self, level: Dict) -> float:
        """Extrae la cantidad (profundidad) de un nivel del libro."""
        if not isinstance(level, dict):
            return 0.0
        for key in ('size', 'quantity', 'remaining', 'vol', 'volume', 'amount'):
            value = level.get(key)
            if value is None:
                continue
            try:
                size = float(value)
                if size >= 0:
                    return size
            except (TypeError, ValueError):
                continue
        return 0.0
    
    def _update_depth_metrics(self, md: Dict) -> Tuple[Optional[float], Optional[float], Optional[float]]:
        """Actualiza precios y profundidades del libro a partir del market data recibido."""
        current_bid = self.market_data.get('bid')
        current_offer = self.market_data.get('offer')
        current_last = self.market_data.get('last')
        current_bid_size = self.market_data.get('bid_size', 0.0)
        current_offer_size = self.market_data.get('offer_size', 0.0)
        current_bid_depth = self.market_data.get('bid_depth', 0.0)
        current_offer_depth = self.market_data.get('offer_depth', 0.0)
        
        if isinstance(md, dict):
            bids = md.get('BI') if isinstance(md.get('BI'), list) else md.get('BI', [])
            offers = md.get('OF') if isinstance(md.get('OF'), list) else md.get('OF', [])
            
            if isinstance(bids, list) and len(bids) > 0 and isinstance(bids[0], dict):
                bid_obj = bids[0]
                bid_price = bid_obj.get('price')
                if isinstance(bid_price, (int, float)):
                    current_bid = float(bid_price)
                current_bid_size = self._extract_level_size(bid_obj)
                current_bid_depth = sum(self._extract_level_size(level)
                                        for level in bids[:self.depth_levels_to_track]
                                        if isinstance(level, dict))
            
            if isinstance(offers, list) and len(offers) > 0 and isinstance(offers[0], dict):
                offer_obj = offers[0]
                offer_price = offer_obj.get('price')
                if isinstance(offer_price, (int, float)):
                    current_offer = float(offer_price)
                current_offer_size = self._extract_level_size(offer_obj)
                current_offer_depth = sum(self._extract_level_size(level)
                                          for level in offers[:self.depth_levels_to_track]
                                          if isinstance(level, dict))
            
            last_obj = md.get('LA')
            if isinstance(last_obj, dict):
                last_price = last_obj.get('price')
                if isinstance(last_price, (int, float)):
                    current_last = float(last_price)
        
        self.market_data.update({
            'bid': current_bid,
            'offer': current_offer,
            'last': current_last,
            'bid_size': current_bid_size,
            'offer_size': current_offer_size,
            'bid_depth': current_bid_depth,
            'offer_depth': current_offer_depth
        })
        
        return self.market_data['bid'], self.market_data['offer'], self.market_data['last']
    
    def _get_pending_entry_quantity(self) -> int:
        """Cantidad pendiente de ejecución en órdenes de entrada activas."""
        total_pending = 0
        try:
            for order_info in self.active_orders.values():
                if order_info.get('role') != 'ENTRY':
                    continue
                remaining = order_info.get('remaining_quantity')
                if remaining is None:
                    quantity = order_info.get('quantity', 0)
                    filled = order_info.get('filled_quantity', 0)
                    remaining = max(0, quantity - filled)
                total_pending += int(max(0, round(remaining)))
        except Exception as e:
            logger.debug(f"[DEPTH] Error calculando entry pendiente: {e}")
        return total_pending
    
    def _handle_entry_execution(self, side: str, executed_qty: float,
                                execution_price: Optional[float],
                                avg_price: Optional[float] = None) -> Tuple[int, int]:
        """Actualiza el estado interno ante ejecuciones de entrada."""
        try:
            qty = int(round(executed_qty))
        except Exception:
            qty = 0
        if qty <= 0:
            return int(round(self.position_quantity)), int(round(self.position_quantity))
        
        prev_qty = int(round(self.position_quantity))
        new_qty = prev_qty + qty
        self.position_quantity = new_qty
        self.position_opened = new_qty > 0
        if side in ('BUY', 'SELL'):
            self.entry_side_actual = side
        elif not self.entry_side_actual:
            self.entry_side_actual = self.entry_side
        
        if self.entry_time is None:
            self.entry_time = time.time()
        
        price_to_use = None
        if isinstance(avg_price, (int, float)) and avg_price > 0:
            price_to_use = float(avg_price)
        elif isinstance(execution_price, (int, float)) and execution_price > 0:
            price_to_use = float(execution_price)
        
        if price_to_use:
            if prev_qty > 0 and isinstance(self.entry_price, (int, float)) and self.entry_price > 0:
                total_value = (self.entry_price * prev_qty) + (price_to_use * qty)
                self.entry_price = total_value / (prev_qty + qty)
            else:
                self.entry_price = price_to_use
        
        if self.position_opened and not self.entry_registered:
            self.register_operation("TRADE_OPEN")
            self.entry_registered = True
        
        if self.position_opened:
            if new_qty >= self.entry_target_quantity:
                self.allow_entry_topup = False
            else:
                self.allow_entry_topup = True
        
        return prev_qty, new_qty
    
    def _handle_exit_execution(self, executed_qty: float) -> Tuple[int, int]:
        """Actualiza la posición ante ejecuciones de cierre."""
        try:
            qty = int(round(executed_qty))
        except Exception:
            qty = 0
        prev_qty = int(round(self.position_quantity))
        if qty <= 0:
            return prev_qty, prev_qty
        
        new_qty = max(0, prev_qty - qty)
        self.position_quantity = new_qty
        self.position_opened = new_qty > 0
        self.allow_entry_topup = False
        self.entry_target_quantity = new_qty if new_qty > 0 else self.order_quantity
        return prev_qty, new_qty
    
    # =============================================================================
    # VALUACIÓN TEÓRICA
    # =============================================================================
    
    def _normalize_rate(self, rate: Optional[float]) -> Optional[float]:
        """Convierte 5.0 -> 0.05 si parece porcentaje; mantiene decimales válidos."""
        if rate is None:
            return None
        try:
            return rate / 100.0 if rate > 1.5 else rate
        except Exception:
            return None
    
    def _days_to_expiry(self) -> int:
        """Usa override si está; de lo contrario asume 30 días como aproximación."""
        if isinstance(self.days_to_expiry_override, (int, float)) and self.days_to_expiry_override > 0:
            return int(self.days_to_expiry_override)
        return 30
    
    def calculate_theoretical_price(self) -> Optional[float]:
        """Calcula precio teórico usando cost of carry (simple/continuous/diferencial)."""
        if not self.spot_price or self.spot_price <= 0:
            return None
        days = self._days_to_expiry()
        if self.use_business_days_for_carry and days > 0:
            days = max(1, int(round(days * 252.0 / 365.0)))
        if days <= 0:
            return None
        t = days / 365.0
        r = self._normalize_rate(self.risk_free_rate)
        r_dom = self._normalize_rate(self.domestic_rate)
        r_for = self._normalize_rate(self.foreign_rate)
        model = (self.valuation_model or 'simple').lower()
        try:
            if model == 'continuous':
                if r is None:
                    return None
                return self.spot_price * math.exp(r * t)
            if model in ('interest_diff', 'interest-diff'):
                if r_dom is None or r_for is None:
                    return None
                denominator = 1 + r_for * t
                if abs(denominator) < 1e-10:  # Evitar división por cero
                    logger.warning(f"[WARNING] Denominador cercano a cero en interest_diff: {denominator}")
                    return None
                return self.spot_price * (1 + r_dom * t) / denominator
            if model in ('interest_diff_continuous', 'interest-diff-continuous'):
                if r_dom is None or r_for is None:
                    return None
                return self.spot_price * math.exp((r_dom - r_for) * t)
            if r is None:
                return None
            return self.spot_price * (1 + r * t)
        except Exception:
            return None
    
    # =============================================================================
    # UTILIDADES DE PRECIO (IMPROVEMENT PARA QUEDAR PRIMERO EN EL BOOK)
    # =============================================================================
    
    def _round_to_tick(self, price: float) -> float:
        """Redondea al múltiplo de tick hacia el precio válido más cercano."""
        if price is None or self.tick_size <= 0:
            return price
        ticks = round(price / self.tick_size)
        return ticks * self.tick_size
    
    def get_improved_price(self, side: str) -> Optional[float]:
        """
        Devuelve un precio mejorado para quedar PRIMERO en el book sin cruzar el spread.
        
        Para BUY (comprar):
          - Objetivo: Quedar primero en el book de COMPRAS (mejor BID)
          - Estrategia: Precio = BID + improvement_ticks (mejorar el mejor BID)
          - Límite: No cruzar el OFFER (no tomar liquidez inmediata)
          
        Para SELL (vender):
          - Objetivo: Quedar primero en el book de VENTAS (mejor OFFER)
          - Estrategia: Precio = OFFER - improvement_ticks (mejorar el mejor OFFER)
          - Límite: No cruzar el BID (no tomar liquidez inmediata)
        """
        logger.debug(f"[FUNC_CALL] [PRICE] get_improved_price() LLAMADO para {side}")
        # Validar tick_size antes de usarlo
        if not self.tick_size or self.tick_size <= 0:
            logger.warning(f"[WARNING] tick_size inválido en get_improved_price: {self.tick_size}")
            return None
        
        bid = self.market_data.get('bid')
        offer = self.market_data.get('offer')
        
        # Validar que tenemos al menos uno de los dos
        if bid is None and offer is None:
            logger.warning(f"[WARNING] No hay bid ni offer para calcular precio mejorado")
            return None
        
        improvement = self.improvement_ticks * self.tick_size
        
        if side == 'BUY':
            # Para BUY: queremos quedar PRIMERO en el book de COMPRAS (mejor BID)
            if bid is None:
                # Si no hay BID, usar OFFER - tick para no tomar liquidez
                if offer is None:
                    return None
                price = offer - self.tick_size
                logger.debug(f"[PRICE_IMPROVEMENT] BUY sin BID: usando {price} (OFFER {offer} - tick {self.tick_size})")
            else:
                # Mejorar el mejor BID en improvement_ticks para quedar primero
                raw_price = bid + improvement
                # No cruzar el OFFER (no tomar liquidez)
                if offer is not None:
                    raw_price = min(raw_price, offer - self.tick_size)
                price = self._round_to_tick(raw_price)
                logger.debug(f"[PRICE_IMPROVEMENT] BUY: BID={bid}, improvement={improvement}, precio_calculado={raw_price}, precio_final={price}, OFFER={offer}")
            
            # Validación final: precio debe ser >= BID (mejorar o igualar) y < OFFER (no cruzar)
            if bid is not None and price < bid:
                logger.warning(f"[WARNING] Precio BUY {price} menor que BID {bid}, ajustando a BID + tick")
                price = self._round_to_tick(bid + self.tick_size)
            
            if offer is not None and price >= offer:
                logger.warning(f"[WARNING] Precio BUY {price} >= OFFER {offer}, ajustando a OFFER - tick")
                price = self._round_to_tick(offer - self.tick_size)
            
            logger.info(f"[PRICE_IMPROVEMENT] BUY final: ${price:.2f} (BID: ${bid:.2f}, OFFER: ${offer:.2f})")
            return price if price and price > 0 else None
            
        else:  # SELL
            # Para SELL: queremos quedar PRIMERO en el book de VENTAS (mejor OFFER)
            # Estrategia: Precio debe ser <= mejor OFFER actual para quedar primero
            # Idealmente: OFFER - improvement_ticks (mejorar el mejor OFFER)
            # Pero nunca cruzar el BID (no tomar liquidez inmediata)
            
            if offer is None:
                # Si no hay OFFER, usar BID + tick para no tomar liquidez
                if bid is None:
                    logger.warning(f"[WARNING] No hay OFFER ni BID para calcular precio SELL")
                    return None
                price = self._round_to_tick(bid + self.tick_size)
                logger.debug(f"[PRICE_IMPROVEMENT] SELL sin OFFER: usando {price} (BID {bid} + tick {self.tick_size})")
                return price
            
            # Calcular precio mejorado: mejorar el mejor OFFER restando improvement
            # Esto nos pone PRIMERO en el book de ventas
            raw_price = offer - improvement
            
            # Verificar que no crucemos el BID (no tomar liquidez)
            if bid is not None:
                min_price = bid + self.tick_size  # Mínimo: BID + 1 tick (no cruzar)
                raw_price = max(raw_price, min_price)
            
            price = self._round_to_tick(raw_price)
            
            # Validación crítica: el precio debe ser <= OFFER para quedar primero
            # Si el cálculo nos da un precio mayor que OFFER, usar OFFER - tick como mínimo
            if price > offer:
                logger.warning(f"[WARNING] Precio SELL {price} > OFFER {offer}, ajustando a OFFER - tick para quedar primero")
                price = self._round_to_tick(offer - self.tick_size)
                # Verificar que aún no cruce el BID
                if bid is not None and price <= bid:
                    price = self._round_to_tick(bid + self.tick_size)
                    logger.warning(f"[WARNING] Precio ajustado {price} <= BID {bid}, usando BID + tick")
            
            # Validación final: precio debe estar en el spread válido
            if bid is not None and price <= bid:
                logger.warning(f"[WARNING] Precio SELL {price} <= BID {bid}, ajustando a BID + tick")
                price = self._round_to_tick(bid + self.tick_size)
                # Pero si esto nos pone arriba del OFFER, hay un problema
                if offer is not None and price > offer:
                    logger.error(f"[ERROR] No se puede calcular precio SELL válido: BID={bid}, OFFER={offer}, spread muy pequeño")
                    # En este caso, usar el mejor precio posible: OFFER - tick
                    price = self._round_to_tick(offer - self.tick_size)
                    if price <= bid:
                        logger.error(f"[ERROR] Spread demasiado pequeño para operar: BID={bid}, OFFER={offer}")
                        return None
            
            # Verificar que el precio quede realmente primero (<= OFFER)
            if offer is not None and price > offer:
                logger.error(f"[ERROR] Precio SELL {price} no queda primero en book (OFFER={offer})")
                return None
            
            logger.info(f"[PRICE_IMPROVEMENT] SELL final: ${price:.2f} (BID: ${bid:.2f}, OFFER: ${offer:.2f})")
            logger.info(f"   - Verificación: Precio <= OFFER: {price <= offer if offer else 'N/A'}, Precio > BID: {price > bid if bid else 'N/A'}")
            
            return price if price and price > 0 else None

    # =============================================================================
    # INICIALIZACIÓN
    # =============================================================================
    
    def initialize(self):
        """Inicializar conexión con pyRofex - MEJORADO para certificación"""
        logger.info("="*70)
        logger.info("[FUNC_CALL] [INIT] initialize() LLAMADO")
        logger.info("="*70)
        try:
            # Credenciales desde variables de entorno (archivo .env o variables del sistema/Spyder)
            username = os.getenv('PRIMARY_USERNAME') or os.getenv('PRIMARY_USER')
            password = os.getenv('PRIMARY_PASSWORD') or os.getenv('PRIMARY_PASS')
            account = os.getenv('PRIMARY_ACCOUNT') or os.getenv('PRIMARY_ACC')
            
            # Debug: mostrar qué variables se encontraron
            logger.info(f"[DEBUG] Variables de entorno encontradas:")
            logger.info(f"   - PRIMARY_USERNAME: {'OK' if os.getenv('PRIMARY_USERNAME') else 'NO'}")
            logger.info(f"   - PRIMARY_USER: {'OK' if os.getenv('PRIMARY_USER') else 'NO'}")
            logger.info(f"   - PRIMARY_PASSWORD: {'OK' if os.getenv('PRIMARY_PASSWORD') else 'NO'}")
            logger.info(f"   - PRIMARY_PASS: {'OK' if os.getenv('PRIMARY_PASS') else 'NO'}")
            logger.info(f"   - PRIMARY_ACCOUNT: {'OK' if os.getenv('PRIMARY_ACCOUNT') else 'NO'}")
            logger.info(f"   - PRIMARY_ACC: {'OK' if os.getenv('PRIMARY_ACC') else 'NO'}")
            
            # Fallback a valores hardcodeados SOLO si no hay variables de entorno (para compatibilidad)
            # Credenciales Matriz OMS Demo:
            # URLs: https://matriz.demo.matrizoms.com.ar/ | https://api.demo.matrizoms.com.ar/
            if not username:
                username = '20458043931'
                logger.warning("ADVERTENCIA: Usando credenciales hardcodeadas. Configura PRIMARY_USERNAME en .env o variables de entorno")
            if not password:
                password = 'Nasdaq161$'
                logger.warning("ADVERTENCIA: Usando credenciales hardcodeadas. Configura PRIMARY_PASSWORD en .env o variables de entorno")
            if not account:
                # Si no se especifica account y el usuario es api_eco, usar cuenta asociada
                if username == 'galo szlomowicz':
                    account = '347751'  # Cuenta asociada a api_eco según documentación (también disponible: '9995')
                    logger.info(f"[INFO] Usuario api_eco detectado - usando cuenta asociada: {account}")
                else:
                    # Para otros usuarios, usar el username como account por defecto
                    account = username or 'api_eco'
                logger.warning("ADVERTENCIA: Usando credenciales hardcodeadas. Configura PRIMARY_ACCOUNT en .env o variables de entorno")
            
            print(f"CREDENCIALES cargadas:")
            print(f"   - Usuario: {username}")
            print(f"   - Password: {'*' * len(password) if password else 'None'}")
            print(f"   - Account: {account}")
            
            if not username or not password or not account:
                logger.error("ERROR: Credenciales incompletas")
                return False
            
            # Configurar URLs personalizadas para Matriz OMS Demo
            # Si las credenciales son de Matriz OMS Demo, usar URLs personalizadas
            if username == 'api_eco' or 'matriz' in username.lower() or os.getenv('USE_MATRIZ_OMS', '').lower() == 'true':
                logger.info("[CONFIG] Configurando pyRofex para Matriz OMS Demo...")
                matriz_api_url = os.getenv('MATRIZ_API_URL', 'https://matriz.eco.xoms.com.ar/')
                matriz_ws_url = os.getenv('MATRIZ_WS_URL', 'wss://matriz.eco.xoms.com.ar/')
                
                # Configurar URLs personalizadas antes de inicializar
                try:
                    pyRofex._set_environment_parameter('url', matriz_api_url, pyRofex.Environment.REMARKET)
                    pyRofex._set_environment_parameter('ws', matriz_ws_url, pyRofex.Environment.REMARKET)
                    logger.info(f"[CONFIG] API URL: {matriz_api_url}")
                    logger.info(f"[CONFIG] WS URL: {matriz_ws_url}")
                except Exception as e:
                    logger.warning(f"[WARNING] No se pudieron configurar URLs personalizadas: {e}")
                    logger.warning("[WARNING] Usando configuración por defecto de pyRofex")
            
            # Configurar pyRofex
            pyRofex.initialize(
                user=username,
                password=password,
                account=account,
                environment=pyRofex.Environment.REMARKET
            )
            
            logger.info("[OK] INICIALIZADO en ambiente: REMARKET")
            logger.info(f"[OK] OPERANDO futuro: {self.future_symbol}")
            
            # Iniciar WebSocket con manejo de errores mejorado
            logger.info("[WS] Conectando WebSocket...")
            try:
                pyRofex.init_websocket_connection(
                    market_data_handler=self._market_data_handler,
                    order_report_handler=self._order_report_handler,
                    error_handler=self._error_handler,
                    exception_handler=self._exception_handler
                )
                self.websocket_connected = True
                self.last_market_data_time = time.time()
                logger.info("[OK] WebSocket inicializado correctamente")
            except Exception as ws_error:
                logger.error(f"[ERROR] Error inicializando WebSocket: {ws_error}")
                logger.error("[ERROR] Intentando reconectar en 5 segundos...")
                time.sleep(5)
                # Reintentar una vez
                try:
                    pyRofex.init_websocket_connection(
                        market_data_handler=self._market_data_handler,
                        order_report_handler=self._order_report_handler,
                        error_handler=self._error_handler,
                        exception_handler=self._exception_handler
                    )
                    self.websocket_connected = True
                    self.last_market_data_time = time.time()
                    logger.info("[OK] WebSocket reconectado exitosamente")
                except Exception as ws_error2:
                    logger.error(f"[ERROR] Falla crítica en WebSocket: {ws_error2}")
                    return False
            
            time.sleep(2)
            
            # Suscribir a market data
            pyRofex.market_data_subscription(
                tickers=[self.future_symbol],
                entries=[
                    pyRofex.MarketDataEntry.BIDS,
                    pyRofex.MarketDataEntry.OFFERS,
                    pyRofex.MarketDataEntry.LAST
                ]
            )
            
            time.sleep(1)
            
            # Suscribir a reportes de órdenes
            pyRofex.order_report_subscription()
            
            logger.info("[OK] WebSocket conectado y suscripciones activas")
            
            # Mostrar configuración
            logger.info("="*70)
            logger.info("CONFIGURACIÓN DE ESTRATEGIA")
            logger.info("="*70)
            logger.info(f"[ENTRY] ENTRADA:")
            logger.info(f"   - Lado: {self.entry_side}")
            if self.entry_side == 'BUY':
                logger.info(f"   - Comprar cuando precio <= ${self.entry_max_price}")
            else:
                logger.info(f"   - Vender cuando precio >= ${self.entry_min_price}")
            logger.info(f"[FILTER] FILTRO:")
            logger.info(f"   - Horario de mercado: {'SI' if self.filter_market_hours_only else 'NO'}")
            logger.info(f"[TARGET] GATILLO:")
            logger.info(f"   - Tipo: {self.trigger_type}")
            logger.info(f"[TARGET] TARGET:")
            logger.info(f"   - Take profit: {self.target_profit_ticks or 'NO'}t")
            logger.info(f"   - Stop loss: {self.target_stop_loss_ticks or 'NO'}t")
            logger.info(f"   - Time exit: {self.target_time_exit_minutes or 'NO'} min")
            logger.info(f"[SYSTEM] SISTEMA:")
            logger.info(f"   - Adaptive speed: {'SI' if self.adaptive_speed else 'NO'}")
            logger.info(f"   - Order timeout: {self.order_timeout_seconds}s")
            logger.info("="*70)
            
            # Iniciar calibración (solo si filtro activo)
            if self.enable_latency_filter:
                self.calibration_start_time = time.time()
                logger.info("")
                logger.info("="*70)
                logger.info("[INFO] INICIANDO CALIBRACION DE LATENCIA (5 minutos)")
                logger.info("[INFO] Durante este periodo el bot NO OPERARA")
                logger.info("[INFO] Solo recopilara muestras para establecer baseline")
                logger.info("="*70)
                logger.info("")
            else:
                logger.info("")
                logger.info("="*70)
                logger.info("[INFO] FILTRO DE LATENCIA DESACTIVADO")
                logger.info("[INFO] El bot operara sin restricciones de latencia")
                logger.info("="*70)
                logger.info("")
            
            return True
            
        except Exception as e:
            # Caso 1.2: Login fallido - Procesa correctamente mensaje de error
            error_str = str(e).lower()
            
            # Detectar tipo de error según el mensaje
            if 'authentication' in error_str or 'login' in error_str or 'credential' in error_str or 'unauthorized' in error_str:
                logger.error(f"[ERROR] ERROR DE AUTENTICACIÓN (Login fallido): {e}")
                logger.error("   Verifica que las credenciales en .env sean correctas")
                print(f"ERROR DE AUTENTICACIÓN (Login fallido): {e}")
                print("   Verifica que las credenciales en .env sean correctas")
                return False
            elif 'connection' in error_str or 'timeout' in error_str or 'network' in error_str:
                logger.error(f"[ERROR] ERROR DE CONEXIÓN: {e}")
                logger.error("   Verifica tu conexión a internet y que el servicio Primary API esté disponible")
                print(f"ERROR DE CONEXIÓN: {e}")
                print("   Verifica tu conexión a internet y que el servicio Primary API esté disponible")
                return False
            else:
                # Otros errores
                logger.error(f"[ERROR] ERROR inicializando: {e}")
                print(f"ERROR inicializando: {e}")
                import traceback
                traceback.print_exc()
                return False
    
    # =============================================================================
    # CALIBRACIÓN DE LATENCIA
    # =============================================================================
    
    def _calibrate_latency_baseline(self):
        """Calibra la línea base de latencia"""
        # Logging throttled - solo cuando hay cambios significativos o cada 30s
        logger.debug(f"[FUNC_CALL] [LATENCY] _calibrate_latency_baseline() LLAMADO - muestras: {len(self.latency_history)}")
        
        if not self.is_calibration_complete:
            if self.calibration_start_time is None:
                return
            
            elapsed = time.time() - self.calibration_start_time
            remaining = self.calibration_period_seconds - elapsed
            
            now = time.time()
            if now - self.last_calibration_status_time >= 30:
                self.last_calibration_status_time = now
                samples = len(self.latency_history)
                # Evitar división por cero
                if self.calibration_period_seconds > 0:
                    progress_pct = (elapsed / self.calibration_period_seconds) * 100
                    remaining_min = remaining / 60.0
                else:
                    progress_pct = 100
                    remaining_min = 0.0
                logger.info(f"[INFO] Calibracion: {progress_pct:.0f}% | Muestras: {samples} | Restante: {remaining_min:.1f} min")
            
            if elapsed >= self.calibration_period_seconds and len(self.latency_history) >= self.min_samples_for_stability:
                self.is_calibration_complete = True
                logger.info("")
                logger.info("="*70)
                logger.info("[OK] CALIBRACION INICIAL COMPLETADA")
                logger.info("="*70)
            else:
                return
        
        if len(self.latency_history) < self.min_samples_for_stability:
            return
        
        # Calcular nuevas métricas
        latencies_ms = [lat * 1000 for lat in self.latency_history]
        
        # CORRECCIÓN: Usar PERCENTIL 75 en lugar de PROMEDIO para baseline
        # Esto permite operar en el 75% de las condiciones (no solo 50%)
        new_baseline = np.percentile(latencies_ms, 75)  # Era: np.mean()
        new_std = np.std(latencies_ms)
        mean_latency = np.mean(latencies_ms)
        min_latency = np.min(latencies_ms)
        max_latency = np.max(latencies_ms)
        
        # Solo actualizar si cambió significativamente (>5%) o si es la primera vez
        baseline_changed = abs(new_baseline - self.latency_baseline_ms) > (self.latency_baseline_ms * 0.05) if self.latency_baseline_ms > 0 else True
        
        # Throttle: solo mostrar logs cada X segundos (o si cambió significativamente)
        now = time.time()
        time_since_last_log = now - self.last_latency_log_time
        should_log = time_since_last_log >= self.latency_log_interval or baseline_changed
        
        # Actualizar valores
        self.latency_baseline_ms = new_baseline
        self.latency_std_baseline_ms = new_std
        self.is_latency_calibrated = True
        
        # Solo mostrar logs si es necesario (throttle o cambio significativo)
        if should_log:
            self.last_latency_log_time = now
            logger.info(f"[OK] LATENCIA CALIBRADA (percentil 75): {self.latency_baseline_ms:.1f}ms")
            logger.info(f"[OK] Rango: mín={min_latency:.1f}ms | promedio={mean_latency:.1f}ms | máx={max_latency:.1f}ms")
            logger.info(f"[OK] Umbral operativo: <= {self.latency_baseline_ms * self.max_latency_multiplier:.1f}ms (opera en 75% de condiciones)")
            logger.info(f"[OK] Muestras analizadas: {len(self.latency_history)}")
            
            # Solo mostrar regla si el filtro está activado
            if self.enable_latency_filter:
                logger.info(f"[INFO] REGLA: Solo opera si latencia <= {self.latency_baseline_ms:.1f}ms")
            
            if self.adaptive_speed:
                self.dynamic_order_interval = max(3, int(self.latency_baseline_ms / 100))
                logger.info(f"[OK] Intervalo de ordenes ajustado a {self.dynamic_order_interval}s")
            
            # Solo mostrar "BOT LISTO" si el filtro está activado
            if self.enable_latency_filter:
                logger.info("[OK] BOT LISTO PARA OPERAR CON EDGE PRESERVADO")
                logger.info("="*70)
                logger.info("")
    
    def check_latency_stability(self) -> Tuple[bool, str]:
        """Verifica si la latencia es estable"""
        logger.debug(f"[FUNC_CALL] [LATENCY_STABLE] check_latency_stability() LLAMADO")
        
        if not self.is_latency_calibrated:
            return True, "Calibrando..."
        
        # Validar que baseline existe y es válido
        if self.latency_baseline_ms is None or self.latency_baseline_ms <= 0:
            logger.warning("[WARNING] Latencia baseline no calibrada correctamente")
            return True, "Calibrando baseline..."
        
        current_latency_ms = self.last_latency * 1000
        
        if current_latency_ms > self.latency_baseline_ms * self.max_latency_multiplier:
            return False, f"Latencia alta {current_latency_ms:.0f}ms > {self.latency_baseline_ms:.0f}ms (pierde edge)"
        
        if len(self.latency_history) >= 5:
            recent_std = np.std([lat * 1000 for lat in list(self.latency_history)[-5:]])
            if recent_std > self.latency_std_baseline_ms * self.max_std_multiplier:
                return False, f"Volatilidad de latencia alta {recent_std:.1f}ms > {self.latency_std_baseline_ms * self.max_std_multiplier:.1f}ms"
        
        return True, f"OK (latencia: {current_latency_ms:.0f}ms <= {self.latency_baseline_ms:.0f}ms)"
    
    # =============================================================================
    # HANDLERS DE WEBSOCKET
    # =============================================================================
    
    def _market_data_handler(self, message):
        """Handler de market data - MIDE LATENCIA REAL DEL MERCADO"""
        # Logging solo cada N mensajes para no saturar (cada 100 mensajes)
        if not hasattr(self, '_md_call_count'):
            self._md_call_count = 0
        self._md_call_count += 1
        
        if self._md_call_count % 100 == 1:
            logger.debug(f"[FUNC_CALL] [MARKET_DATA] _market_data_handler() llamado ({self._md_call_count} veces)")
        
        try:
            if message.get('type') == 'Md':
                symbol = message.get('instrumentId', {}).get('symbol')
                if symbol == self.future_symbol:
                    # MEDIR LATENCIA REAL
                    receive_time = time.time()
                    server_timestamp = message.get('timestamp')
                    
                    if server_timestamp:
                        try:
                            server_time = server_timestamp / 1000.0
                            latency = receive_time - server_time
                            
                            if 0 < latency < 10:
                                self.last_latency = latency
                                self.latency_history.append(latency)
                                self.latency_timestamps.append(datetime.now())
                                
                                # Guardar latencia en CSV
                                self._log_latency_to_csv(latency * 1000)
                                
                                # Actualizar gráfico en vivo si está habilitado
                                if self.plot_latency_live:
                                    self._update_latency_plot()
                                
                                self._calibrate_latency_baseline()
                                
                                self.alert_throttle_count += 1
                                if latency > self.latency_warning_threshold and self.alert_throttle_count % 20 == 0:
                                    logger.warning(f"[WARNING] Latencia del mercado alta: {latency*1000:.0f}ms")
                        except Exception as e:
                            logger.debug(f"No se pudo calcular latencia: {e}")
                    
                    # Actualizar datos del mercado
                    md = message.get('marketData', {})
                    old_bid = self.market_data.get('bid')
                    old_offer = self.market_data.get('offer')
                    old_last = self.market_data.get('last')
                    bid, offer, last = self._update_depth_metrics(md)
                    
                    # Log ocasional para debug (cada 60 segundos máximo)
                    now = time.time()
                    if not hasattr(self, '_last_md_log_time') or (now - getattr(self, '_last_md_log_time', 0)) >= 60:
                        self._last_md_log_time = now
                        logger.debug(f"[DEBUG] WebSocket Market Data recibido:")
                        logger.debug(f"   - Timestamp servidor: {server_timestamp if server_timestamp else 'N/A'}")
                        logger.debug(f"   - Timestamp recepcion: {receive_time:.3f}")
                        logger.debug(f"   - BI (array completo): {md.get('BI', [])}")
                        logger.debug(f"   - OF (array completo): {md.get('OF', [])}")
                        logger.debug(f"   - TOP BID extraido: {bid}")
                        logger.debug(f"   - TOP OFFER extraido: {offer}")
                        logger.debug(f"   - LAST: {last}")
                    
                    # Actualizar timestamp de última data recibida (para health check)
                    self.last_market_data_time = receive_time
                    self.market_data['timestamp'] = receive_time
                    
                    # Log detallado de cambios en el book (cada 10 segundos o si cambió significativamente)
                    log_md = False
                    now = time.time()
                    if not hasattr(self, '_last_md_detailed_log_time') or (now - getattr(self, '_last_md_detailed_log_time', 0)) >= 10:
                        log_md = True
                        self._last_md_detailed_log_time = now
                    
                    # También loggear si cambió significativamente
                    if bid and old_bid and abs(bid - old_bid) > self.tick_size * 2:
                        log_md = True
                    if offer and old_offer and abs(offer - old_offer) > self.tick_size * 2:
                        log_md = True
                    
                    if log_md:
                        bid_price = self.market_data.get('bid')
                        offer_price = self.market_data.get('offer')
                        last_price = self.market_data.get('last', 0) or 0
                        
                        # Validar que bid y offer existan antes de formatear
                        bid_str = f"${bid_price:.2f}" if bid_price is not None else "N/A"
                        offer_str = f"${offer_price:.2f}" if offer_price is not None else "N/A"
                        last_str = f"${last_price:.2f}" if last_price else "N/A"
                        
                        logger.info(f"[BOOK] {self.future_symbol} - BID: {bid_str} | OFFER: {offer_str} | LAST: {last_str}")
                        if bid_price is not None and offer_price is not None:
                            spread = offer_price - bid_price
                            if self.tick_size and self.tick_size > 0:
                                logger.info(f"[BOOK] Spread: ${spread:.2f} ({spread/self.tick_size:.1f} ticks)")
                            else:
                                logger.info(f"[BOOK] Spread: ${spread:.2f}")
                        bid_size = self.market_data.get('bid_size', 0.0)
                        offer_size = self.market_data.get('offer_size', 0.0)
                        bid_depth = self.market_data.get('bid_depth', 0.0)
                        offer_depth = self.market_data.get('offer_depth', 0.0)
                        logger.info(f"[DEPTH] BID size: {bid_size:.0f} | OFFER size: {offer_size:.0f} | "
                                    f"Profundidad {self.depth_levels_to_track} niveles → BID: {bid_depth:.0f} | OFFER: {offer_depth:.0f}")
                    
                    # Verificar timeout de órdenes SIEMPRE (importante para órdenes de cierre)
                    if self.running:
                        self.check_order_timeout()
                    
                    # CRÍTICO: Verificar precios fijos de salida INSTANTÁNEAMENTE (prioridad máxima)
                    # Esto debe ejecutarse ANTES de cualquier otra verificación
                    if self.running and self.position_opened and self.fixed_exit_prices:
                        # Verificar precios fijos inmediatamente sin esperar al ciclo normal
                        if len(self.active_orders) == 0 and not self.active_order and not self._order_lock:
                            try:
                                exit_result, exit_reason = self.check_exit_conditions()
                                if exit_result:
                                    logger.info(f"[MARKET_DATA] [FIXED_PRICE] Precio fijo alcanzado - ejecutando salida inmediata")
                                    # Si es salida completa (no parcial), llamar close_position
                                    if exit_reason and exit_reason.startswith("FIXED_PRICE") and "_FULL" in exit_reason:
                                        logger.info(f"[MARKET_DATA] [FIXED_PRICE] Cerrando posición completa - razón: {exit_reason}")
                                        self.close_position(exit_reason)
                                    # Si es parcial, ya fue ejecutada en check_exit_conditions
                            except Exception as e:
                                logger.error(f"[MARKET_DATA] [ERROR] Error verificando precios fijos: {e}")
                                import traceback
                                logger.error(traceback.format_exc())
                    
                    # CRÍTICO: Verificar oportunidad SIEMPRE (entrada o salida según estado)
                    # - Si NO hay posición: verifica condiciones de ENTRADA
                    # - Si HAY posición: verifica condiciones de SALIDA
                    if self.running:
                        # Solo bloquear si hay órdenes activas pendientes (no posición abierta)
                        if len(self.active_orders) > 0 or self.active_order:
                            logger.debug(f"[MARKET_DATA] NO verificando oportunidad: hay órdenes activas ({len(self.active_orders)})")
                        else:
                            # Siempre llamar check_trading_opportunity - ella maneja posición abierta/cerrada
                            # Si position_opened=True, verificará condiciones de SALIDA
                            # Si position_opened=False, verificará condiciones de ENTRADA
                            self.check_trading_opportunity()
        
        except Exception as e:
            logger.error(f"[ERROR] Error en market data handler: {e}")
    
    def _order_report_handler(self, message):
        """
        Handler de reportes de órdenes del WebSocket
        
        Según manual Primary-API.pdf (páginas 23-24):
        El mensaje viene con estructura:
        {
          "type": "or",
          "timestamp": timestamp,
          "orderReport": {
            "orderId": "xxx",           # Order ID del mercado
            "clOrdId": "yyy",           # Client Order ID (el que usamos para cancelar)
            "proprietary": "api",
            "status": "NEW/FILLED/etc",
            "text": "descripción",
            ...
          }
        }
        
        Estados posibles: PENDING_NEW, NEW, PARTIALLY_FILLED, FILLED, CANCELLED, REJECTED
        """
        logger.info(f"[FUNC_CALL] [ORDER_REPORT] _order_report_handler() LLAMADO")
        try:
            if message.get('type') == 'OR':
                # Extraer orderReport según estructura del manual Primary API
                # Según manual: el mensaje puede tener 'orderReport' o venir directamente
                order_report = message.get('orderReport', message)
                
                # Campos según documentación Primary API (páginas 23-24, 37):
                # - clOrdId: Client Order ID (el que enviamos, usado para cancelar)
                # - orderId: Order ID del mercado (asignado por el exchange)
                # - status: Estado (NEW, FILLED, CANCELLED, REJECTED, etc.)
                # - proprietary: ID del participante
                # - avgPx: Precio promedio de ejecución (solo si hay ejecución)
                # - cumQty: Cantidad acumulada ejecutada
                # - leavesQty: Cantidad pendiente
                # - lastPx, lastQty: Último precio y cantidad ejecutada
                cl_ord_id = order_report.get('clOrdId')  # Client Order ID (para cancelar)
                order_id = order_report.get('orderId')    # Order ID del mercado
                status = order_report.get('status')         # Estado actual
                text = order_report.get('text', '')         # Descripción/motivo
                proprietary_from_report = order_report.get('proprietary', '')
                
                # CRÍTICO: Actualizar proprietary si viene en el report y no lo tenemos guardado
                if proprietary_from_report and cl_ord_id in self.active_orders:
                    if not self.active_orders[cl_ord_id].get('proprietary'):
                        self.active_orders[cl_ord_id]['proprietary'] = proprietary_from_report
                        logger.debug(f"[ORDER_REPORT] Actualizado proprietary para {cl_ord_id}: {proprietary_from_report}")
                
                # Validar que cl_ord_id existe
                if not cl_ord_id:
                    logger.warning(f"[WARNING] Order report sin clOrdId, ignorando: {message}")
                    return
                
                # Validar que status existe
                if not status:
                    logger.warning(f"[WARNING] Order report sin status para clOrdId={cl_ord_id}, ignorando")
                    return
                
                # Log del mensaje recibido (debug)
                logger.debug(f"[ORDER_REPORT] Recibido: clOrdId={cl_ord_id}, orderId={order_id}, status={status}")
                
                # Solo procesar órdenes que hemos enviado nosotros
                if cl_ord_id not in self.active_orders:
                    logger.debug(f"[ORDER_REPORT] Orden {cl_ord_id} no está en active_orders, ignorando")
                    # Si es un estado terminal, limpiar flags por si acaso
                    if status in ['FILLED', 'CANCELLED', 'REJECTED']:
                        if cl_ord_id in self.order_cancel_pending:
                            self.order_cancel_pending.discard(cl_ord_id)
                        if cl_ord_id in self.orders_price_improved:
                            self.orders_price_improved.discard(cl_ord_id)
                    return
                
                # CRÍTICO: Verificar estado actual antes de procesar
                current_state_before = self.order_states.get(cl_ord_id, 'UNKNOWN')
                
                # Si ya está en estado terminal y recibimos otro report del mismo estado, puede ser duplicado
                if current_state_before in ['FILLED', 'CANCELLED', 'REJECTED'] and status == current_state_before:
                    logger.debug(f"[ORDER_REPORT] Orden {cl_ord_id} ya está en estado {status}, ignorando report duplicado")
                    return
                
                if cl_ord_id in self.active_orders:
                    old_status = self.order_states.get(cl_ord_id, 'UNKNOWN')
                    self.order_states[cl_ord_id] = status
                    
                    # Guardar orderId si viene (importante para tracking completo)
                    if order_id and 'order_id' not in self.active_orders[cl_ord_id]:
                        self.active_orders[cl_ord_id]['order_id'] = order_id
                        logger.debug(f"[ORDER] Guardado orderId={order_id} para clOrdId={cl_ord_id}")
                    
                    # Log del cambio de estado con ambos IDs
                    order_id_str = f" (orderId={order_id})" if order_id else ""
                    logger.info(f"[ORDER] clOrdId={cl_ord_id}{order_id_str}: {old_status} -> {status} | {text}")
                    
                    # Manejar cada estado
                    logger.info(f"[ORDER_STATUS] Procesando cambio de estado: {old_status} -> {status}")
                    
                    if status == 'PENDING_NEW':
                        logger.info(f"[ORDER_STATUS] [PENDING] Orden en estado PENDING_NEW - esperando confirmación del mercado")
                        logger.info(f"[ORDER_STATUS] Acción: Continuar esperando ExecutionReport...")
                        # CRÍTICO: No hacer nada más, solo actualizar estado
                    
                    elif status == 'NEW':
                        logger.info(f"[ORDER_STATUS] [OK] Orden aceptada en el mercado (status=NEW)")
                        logger.info(f"[ORDER_STATUS] Acción: Orden está activa en el book esperando ejecución")
                        # No registrar en CSV - estado intermedio (solo se registran FILLED/CANCELLED/REJECTED)
                    
                    elif status == 'REJECTED':
                        logger.error(f"[ORDER_STATUS] [ERROR] Orden rechazada por el mercado")
                        logger.error(f"[ORDER_STATUS] Razón: {text}")
                        logger.error(f"[ORDER_STATUS] Acción: Limpiando orden de active_orders y permitiendo nueva orden")
                        logger.error(f"[ORDER_STATUS] Registrando rechazo en CSV...")
                        self._log_order_to_csv(
                            cl_ord_id, 
                            self.active_orders[cl_ord_id]['side'], 
                            self.active_orders[cl_ord_id]['price'], 
                            self.active_orders[cl_ord_id]['quantity'],
                            'REJECTED'
                        )
                        # Limpiar flag de mejora de precio
                        if cl_ord_id in self.orders_price_improved:
                            self.orders_price_improved.discard(cl_ord_id)
                            logger.info(f"[ORDER_STATUS] Flag de mejora de precio limpiado para {cl_ord_id}")
                        del self.active_orders[cl_ord_id]
                        if cl_ord_id in self.order_states:
                            del self.order_states[cl_ord_id]
                        if self.active_order == cl_ord_id:
                            self.active_order = None
                        logger.info(f"[ORDER_STATUS] [OK] Orden rechazada limpiada. Órdenes activas restantes: {len(self.active_orders)}")
                    
                    elif status == 'PARTIALLY_FILLED':
                        order_info = self.active_orders.get(cl_ord_id)
                        if not order_info:
                            logger.warning(f"[EJECUCION] Ejecución parcial para orden desconocida {cl_ord_id}")
                            return
                        
                        cum_qty = order_report.get('cumQty', 0) or order_report.get('cumQuantity', 0)
                        leaves_qty = order_report.get('leavesQty', 0) or order_report.get('leavesQuantity', 0)
                        avg_px = order_report.get('avgPx', 0)
                        last_px = order_report.get('lastPx', 0)
                        last_qty = order_report.get('lastQty', 0)
                        total_qty = order_info.get('quantity', 0)
                        prev_filled = order_info.get('filled_quantity', 0)
                        executed_delta = max(0, (cum_qty or 0) - prev_filled)
                        if executed_delta <= 0 and last_qty:
                            executed_delta = last_qty
                        if executed_delta <= 0:
                            executed_delta = max(0, total_qty - prev_filled - leaves_qty)
                        
                        order_info['filled_quantity'] = cum_qty
                        order_info['remaining_quantity'] = leaves_qty
                        if avg_px and avg_px > 0:
                            order_info['avg_price'] = avg_px
                        
                        logger.info(f"[EJECUCION] EJECUCIÓN PARCIAL detectada en orden {cl_ord_id}:")
                        logger.info(f"   - Cantidad original: {total_qty}")
                        logger.info(f"   - Ejecutado (incremental): {executed_delta}")
                        logger.info(f"   - Total ejecutado (CumQty): {cum_qty}")
                        logger.info(f"   - Remanente (LeavesQty): {leaves_qty}")
                        logger.info(f"   - Precio promedio: ${avg_px:.2f} | Último precio: ${last_px:.2f}")
                        
                        order_role = order_info.get('role') or ('ENTRY' if order_info.get('side') == self.entry_side else 'EXIT')
                        if order_role == 'ENTRY':
                            prev_qty, new_qty = self._handle_entry_execution(
                                order_info.get('side'),
                                executed_delta,
                                last_px or avg_px or order_info.get('price'),
                                avg_px
                            )
                            logger.info(f"[ENTRY] Parcial ejecutada → posición: {prev_qty} -> {new_qty}")
                        elif order_role in ('EXIT', 'PARTIAL_EXIT'):
                            prev_qty, new_qty = self._handle_exit_execution(executed_delta)
                            logger.info(f"[EXIT] Parcial ejecutada → posición: {prev_qty} -> {new_qty}")
                        else:
                            logger.debug(f"[EJECUCION] Rol desconocido para orden {cl_ord_id}: {order_role}")
                    
                    elif status == 'CANCELLED':
                        logger.info(f"[ORDER_STATUS] [CANCELLED] Orden cancelada")
                        logger.info(f"[ORDER_STATUS] Motivo: {text}")
                        logger.info(f"[ORDER_STATUS] [OK] CONFIRMACIÓN DE CANCELACIÓN RECIBIDA DEL MERCADO")
                        logger.info(f"[ORDER_STATUS] Acción: Limpiando orden y permitiendo nueva orden")
                        self._log_order_to_csv(
                            cl_ord_id, 
                            self.active_orders[cl_ord_id]['side'], 
                            self.active_orders[cl_ord_id]['price'], 
                            self.active_orders[cl_ord_id]['quantity'],
                            'CANCELLED'
                        )
                        # limpiar flags de cancelación - CRÍTICO: esto permite que se envíen nuevas órdenes
                        if cl_ord_id in self.order_cancel_pending:
                            self.order_cancel_pending.discard(cl_ord_id)
                            logger.info(f"[ORDER_STATUS] [OK] Flag de cancelación pendiente limpiado - NUEVAS ÓRDENES PERMITIDAS")
                        else:
                            logger.info(f"[ORDER_STATUS] Orden cancelada pero no estaba en order_cancel_pending (cancelación externa?)")
                        # Limpiar flag de mejora de precio
                        if cl_ord_id in self.orders_price_improved:
                            self.orders_price_improved.discard(cl_ord_id)
                            logger.info(f"[ORDER_STATUS] Flag de mejora de precio limpiado")
                        del self.active_orders[cl_ord_id]
                        if cl_ord_id in self.order_states:
                            del self.order_states[cl_ord_id]
                        if self.active_order == cl_ord_id:
                            self.active_order = None
                        logger.info(f"[ORDER_STATUS] [OK] Orden cancelada limpiada. Órdenes activas restantes: {len(self.active_orders)}")
                        logger.info(f"[ORDER_STATUS] [OK] NUEVAS ÓRDENES PERMITIDAS - No hay órdenes pendientes de cancelación")
                    
                    elif status == 'FILLED':
                        order_info = self.active_orders.get(cl_ord_id)
                        if not order_info:
                            logger.error(f"[ERROR] FILLED recibido para orden {cl_ord_id} que no está en active_orders")
                            return
                        
                        avg_px = order_report.get('avgPx', 0)
                        cum_qty = order_report.get('cumQty', 0) or order_report.get('cumQuantity', 0)
                        leaves_qty = order_report.get('leavesQty', 0) or order_report.get('leavesQuantity', 0)
                        last_px = order_report.get('lastPx', 0)
                        last_qty = order_report.get('lastQty', 0)
                        prev_filled = order_info.get('filled_quantity', 0)
                        executed_delta = max(0, (cum_qty or 0) - prev_filled)
                        if executed_delta <= 0 and last_qty:
                            executed_delta = last_qty
                        if executed_delta <= 0:
                            executed_delta = max(0, order_info.get('quantity', 0) - prev_filled)
                        
                        order_info['filled_quantity'] = cum_qty if cum_qty else order_info.get('quantity', 0)
                        order_info['remaining_quantity'] = 0
                        if avg_px and avg_px > 0:
                            order_info['avg_price'] = avg_px
                        filled_price = avg_px if avg_px and avg_px > 0 else order_info.get('price')
                        execution_price = last_px if last_px and last_px > 0 else filled_price
                        
                        logger.info("=" * 70)
                        logger.info(f"[EJECUCION] EJECUCIÓN TOTAL detectada en orden {cl_ord_id}:")
                        logger.info(f"   - Cantidad ejecutada total: {cum_qty if cum_qty else order_info.get('quantity')}")
                        logger.info(f"   - Incremento final ejecutado: {executed_delta}")
                        logger.info(f"   - Precio promedio: ${avg_px:.2f}")
                        logger.info(f"   - Último precio: ${last_px:.2f}")
                        if leaves_qty and leaves_qty > 0:
                            logger.warning(f"[EJECUCION] LeavesQty reportado > 0 en FILLED: {leaves_qty}")
                        logger.info("=" * 70)
                        
                        self._log_order_to_csv(
                            cl_ord_id, 
                            order_info['side'], 
                            order_info['price'], 
                            order_info['quantity'],
                            'FILLED',
                            filled_price
                        )
                        
                        order_role = order_info.get('role') or ('ENTRY' if order_info.get('side') == self.entry_side else 'EXIT')
                        if order_role == 'ENTRY':
                            prev_qty, new_qty = self._handle_entry_execution(
                                order_info.get('side'),
                                executed_delta,
                                execution_price,
                                avg_px
                            )
                            logger.info(f"[ENTRY] Orden completada. Posición: {prev_qty} -> {new_qty}")
                        elif order_role in ('EXIT', 'PARTIAL_EXIT'):
                            prev_qty, new_qty = self._handle_exit_execution(executed_delta)
                            logger.info(f"[EXIT] Orden completada. Posición: {prev_qty} -> {new_qty}")
                            
                            if new_qty == 0:
                                pnl_ticks = 0
                                if self.tick_size and self.tick_size > 0 and self.entry_price and self.entry_side_actual:
                                    if self.entry_side_actual == 'BUY':
                                        pnl_ticks = (filled_price - self.entry_price) / self.tick_size
                                    else:
                                        pnl_ticks = (self.entry_price - filled_price) / self.tick_size
                                else:
                                    logger.warning(f"[WARNING] No se pudo calcular P&L: entry_price={self.entry_price}, entry_side_actual={self.entry_side_actual}, tick_size={self.tick_size}")
                                
                                if self.entry_time:
                                    duracion_min = (time.time() - self.entry_time) / 60.0
                                else:
                                    logger.warning(f"[WARNING] entry_time es None, usando 0 para duración")
                                    duracion_min = 0.0
                                
                                exit_reason = getattr(self, 'last_exit_reason', 'MANUAL')
                                closed_quantity = prev_qty if prev_qty > 0 else executed_delta
                                self._log_trade_to_csv(
                                    self.entry_side_actual,
                                    self.entry_price,
                                    filled_price,
                                    pnl_ticks,
                                    duracion_min,
                                    exit_reason,
                                    quantity=closed_quantity
                                )
                                
                                self.register_operation("TRADE_CLOSE")
                                logger.info(f"[OK] POSICIÓN CERRADA: P&L = {pnl_ticks:+.1f} ticks | Cantidad: {closed_quantity}")
                                
                                self.position_opened = False
                                self.entry_price = None
                                self.entry_time = None
                                self.entry_side_actual = None
                                self.position_quantity = 0
                                self.entry_registered = False
                                self.last_close_time = time.time()
                                logger.info(f"[OK] Estado reseteado tras cierre total")
                        else:
                            logger.debug(f"[EJECUCION] Rol desconocido '{order_role}' para orden FILLED {cl_ord_id}")
                        
                        if cl_ord_id in self.orders_price_improved:
                            self.orders_price_improved.discard(cl_ord_id)
                        del self.active_orders[cl_ord_id]
                        if cl_ord_id in self.order_states:
                            del self.order_states[cl_ord_id]
                        if cl_ord_id in self.order_cancel_pending:
                            self.order_cancel_pending.discard(cl_ord_id)
                        if self.active_order == cl_ord_id:
                            self.active_order = None
        
        except Exception as e:
            logger.error(f"[ERROR] Error en order report handler: {e}")
    
    def _error_handler(self, message):
        """Handler de errores del WebSocket"""
        logger.info(f"[FUNC_CALL] [ERROR] _error_handler() LLAMADO")
        logger.error(f"[ERROR] WebSocket error: {message}")
        
        # Detectar errores críticos que requieren reconexión
        error_str = str(message).lower()
        critical_keywords = ['connection', 'timeout', 'disconnected', 'closed', 'broken', 'io error', 'network']
        
        if any(keyword in error_str for keyword in critical_keywords):
            logger.warning(f"[WARNING] Error crítico detectado - intentando reconectar WebSocket...")
            self.websocket_connected = False
            self._reconnect_websocket()
    
    def _exception_handler(self, e):
        """Handler de excepciones del WebSocket"""
        logger.info(f"[FUNC_CALL] [EXCEPTION] _exception_handler() LLAMADO")
        logger.error(f"[ERROR] WebSocket exception: {e}")
        import traceback
        logger.error(f"[ERROR] Traceback:\n{traceback.format_exc()}")
        
        # Detectar excepciones críticas
        exception_str = str(e).lower()
        critical_keywords = ['connection', 'timeout', 'broken', 'io', 'network', 'socket']
        
        if any(keyword in exception_str for keyword in critical_keywords):
            logger.warning(f"[WARNING] Excepción crítica detectada - intentando reconectar WebSocket...")
            self.websocket_connected = False
            self._reconnect_websocket()
    
    # =============================================================================
    # LÓGICA DE TRADING
    # =============================================================================
    
    def check_entry_conditions(self) -> bool:
        """Verifica condiciones de entrada basadas en PRECIO o VALUACIÓN."""
        # Modo valuación teórica
        if self.use_theoretical_valuation:
            theo = self.calculate_theoretical_price()
            if theo is None or theo <= 0:
                return False
            
            current_price = self.market_data.get('offer' if self.entry_side == 'BUY' else 'bid')
            if current_price is None or current_price <= 0:
                return False
            
            diff_pct = ((current_price - theo) / theo) * 100.0
            threshold = abs(self.cheap_threshold_pct) if self.entry_side == 'BUY' else abs(self.expensive_threshold_pct)
            
            if self.entry_side == 'BUY':
                if diff_pct <= -threshold:
                    logger.info(f"[OK] ENTRADA BUY: ${current_price:.2f} vs teórico ${theo:.2f} ({diff_pct:+.2f}%)")
                    return True
            else:
                if diff_pct >= threshold:
                    logger.info(f"[OK] ENTRADA SELL: ${current_price:.2f} vs teórico ${theo:.2f} ({diff_pct:+.2f}%)")
                    return True
            return False

        # Modo precio puro
        current_price = self.market_data.get('offer' if self.entry_side == 'BUY' else 'bid')
        if not current_price or not isinstance(current_price, (int, float)):
            return False
        
        if self.entry_side == 'BUY':
            if not hasattr(self, 'entry_max_price') or not self.entry_max_price:
                return False
            if current_price <= self.entry_max_price:
                if self.min_depth_contracts > 0:
                    depth_available = self.market_data.get('offer_depth', 0.0)
                    if depth_available is None or depth_available < self.min_depth_contracts:
                        logger.debug(f"[ENTRY] Profundidad insuficiente para BUY: depth={depth_available}, requerido={self.min_depth_contracts}")
                        return False
                logger.info(f"[OK] ENTRADA BUY: ${current_price:.2f} <= ${self.entry_max_price:.2f}")
                return True
        else:
            if not hasattr(self, 'entry_min_price') or not self.entry_min_price:
                return False
            if current_price >= self.entry_min_price:
                if self.min_depth_contracts > 0:
                    depth_available = self.market_data.get('bid_depth', 0.0)
                    if depth_available is None or depth_available < self.min_depth_contracts:
                        logger.debug(f"[ENTRY] Profundidad insuficiente para SELL: depth={depth_available}, requerido={self.min_depth_contracts}")
                        return False
                logger.info(f"[OK] ENTRADA SELL: ${current_price:.2f} >= ${self.entry_min_price:.2f}")
                return True
        return False
    
    def check_filter_conditions(self) -> bool:
        """Verifica filtros"""
        # Filtro 1: Datos frescos
        timestamp = self.market_data.get('timestamp')
        if not timestamp or (time.time() - timestamp) > self.filter_max_data_age_seconds:
            return False
        
        # Filtro 2: Latencia estable (solo si está habilitado)
        if self.enable_latency_filter:
            is_stable, _ = self.check_latency_stability()
            if not is_stable:
                return False
        
        # Filtro 3: Horario de mercado
        if self.filter_market_hours_only:
            now = datetime.now()
            if now.weekday() >= 5 or not (11 <= now.hour < 17):
                return False
        
        return True
    
    def execute_trigger(self) -> Optional[float]:
        """Determina precio de ejecución"""
        bid = self.market_data.get('bid')
        offer = self.market_data.get('offer')
        
        if not bid or not offer or not isinstance(bid, (int, float)) or not isinstance(offer, (int, float)):
            return None
        
        if self.trigger_type == "IMMEDIATE":
            price = offer if self.entry_side == 'BUY' else bid
            logger.info(f"[OK] GATILLO IMMEDIATE: {self.entry_side}@${price:.2f}")
            return float(price) if price else None
        
        elif self.trigger_type == "BID_OFFER_TOUCH":
            price = bid if self.entry_side == 'BUY' else offer
            logger.info(f"[OK] GATILLO TOUCH: {self.entry_side}@${price:.2f}")
            return float(price) if price else None
        
        elif self.trigger_type == "PRICE_IMPROVEMENT":
            # Verificar si ya hay orden mejorada activa
            if self.allow_price_improvement_once and len(self.active_orders) > 0:
                for cl_ord_id in self.active_orders.keys():
                    if cl_ord_id in self.orders_price_improved:
                        price = offer if self.entry_side == 'BUY' else bid
                        logger.info(f"[OK] GATILLO (sin mejora, ya mejorada): {self.entry_side}@${price:.2f}")
                        return float(price) if price else None
            
            price = self.get_improved_price(self.entry_side)
            if price:
                logger.info(f"[OK] GATILLO MEJORADO: {self.entry_side}@${price:.2f}")
            return price
        
        return None
    
    def _get_dynamic_tp(self, minutes_in_position: float) -> Tuple[float, str]:
        """
        Calcula el TP dinámico según el tiempo transcurrido (degradación progresiva).
        
        Lógica:
        - 0-1 min: TP = tp_initial_ticks (ej: 1 tick)
        - 1-2 min: TP = tp_degraded_ticks (ej: 0.5 ticks)
        - 2-3 min: TP = 0 (break even)
        - 3+ min: Aplicar stop loss
        
        Returns:
            Tuple[float, str]: (tp_ticks, estado) donde estado es 'INITIAL', 'DEGRADED', 'BREAK_EVEN', 'STOP_LOSS'
        """
        if not self.time_based_tp_enabled:
            # Si no está habilitado, usar TP estándar
            return self.target_profit_ticks or 0, 'STANDARD'
        
        if minutes_in_position < self.tp_degradation_time_minutes:
            # Primer minuto: TP inicial
            return self.tp_initial_ticks, 'INITIAL'
        elif minutes_in_position < self.tp_break_even_time_minutes:
            # Después del primer minuto: TP degradado
            return self.tp_degraded_ticks, 'DEGRADED'
        elif minutes_in_position < self.tp_stop_loss_time_minutes:
            # Después del segundo minuto: Break even (TP = 0)
            return 0.0, 'BREAK_EVEN'
        else:
            # Después del tercer minuto: Aplicar stop loss
            return -self.target_stop_loss_ticks if self.target_stop_loss_ticks else 0, 'STOP_LOSS'
    
    def check_exit_conditions(self) -> Tuple[bool, str]:
        """Verifica condiciones de salida"""
        logger.info(f"[EXIT] ========== VERIFICANDO CONDICIONES DE SALIDA ==========")
        logger.info(f"[EXIT] check_exit_conditions() LLAMADO")
        
        if not self.position_opened:
            logger.debug(f"[EXIT] No hay posición abierta - saliendo sin verificar")
            return False, ""
        
        # VALIDACIÓN: Verificar que la posición esté completa antes de permitir salidas
        # ============================================================================
        position_qty = int(round(self.position_quantity)) if hasattr(self, 'position_quantity') else 0
        pending_entry_qty = self._get_pending_entry_quantity()
        target_entry_qty = int(round(self.entry_target_quantity if hasattr(self, 'entry_target_quantity') else self.order_quantity))
        total_expected_qty = position_qty + pending_entry_qty
        
        logger.info(f"[EXIT] Verificando completitud de posición...")
        logger.info(f"[EXIT]   - Posición ejecutada: {position_qty} contratos")
        logger.info(f"[EXIT]   - Pendiente de ejecutar: {pending_entry_qty} contratos")
        logger.info(f"[EXIT]   - Total esperado: {total_expected_qty} contratos")
        logger.info(f"[EXIT]   - Objetivo: {target_entry_qty} contratos")
        
        if total_expected_qty < target_entry_qty:
            remaining_qty = target_entry_qty - total_expected_qty
            logger.warning(f"[EXIT] [BLOQUEADO] Posición incompleta: faltan {remaining_qty} contrato(s) para alcanzar objetivo de {target_entry_qty}")
            logger.warning(f"[EXIT] [BLOQUEADO] Esperando completar posición antes de permitir salidas")
            return False, "POSITION_INCOMPLETE"
        
        logger.info(f"[EXIT] [OK] Posición completa: {position_qty} ejecutados + {pending_entry_qty} pendientes = {total_expected_qty} >= {target_entry_qty}")
        
        logger.info(f"[EXIT] Verificando condiciones de salida...")
        logger.info(f"[EXIT] Posición actual: {self.entry_side_actual} @ ${self.entry_price:.2f}" if self.entry_price else "[EXIT] Posición: sin precio")
        if self.entry_time:
            logger.info(f"[EXIT] Tiempo en posición: {(time.time() - self.entry_time) / 60:.1f} min")
        else:
            logger.info(f"[EXIT] Tiempo en posición: sin timestamp")
        
        # Validaciones críticas
        if not self.entry_price or not self.tick_size or self.tick_size <= 0:
            logger.warning(f"[EXIT_CHECK] [ERROR] Datos inválidos: entry_price={self.entry_price}, tick_size={self.tick_size}")
            return False, ""
        
        # Validar entry_side_actual
        if not self.entry_side_actual or self.entry_side_actual not in ('BUY', 'SELL'):
            logger.warning(f"[EXIT_CHECK] [ERROR] entry_side_actual inválido: {self.entry_side_actual}")
            return False, ""
        
        # Calcular P&L actual
        current_pnl_ticks = 0
        current_price = None
        bid_price = self.market_data.get('bid')
        offer_price = self.market_data.get('offer')
        
        if bid_price is not None and offer_price is not None:
            if self.entry_side_actual == 'BUY':
                current_price = bid_price
                if current_price is not None and self.entry_price is not None:
                    if self.tick_size and self.tick_size > 0:
                        current_pnl_ticks = (current_price - self.entry_price) / self.tick_size
                    else:
                        logger.warning(f"[EXIT_CHECK] [ERROR] tick_size inválido: {self.tick_size}")
                        return False, ""
            else:
                current_price = offer_price
                if current_price is not None and self.entry_price is not None:
                    if self.tick_size and self.tick_size > 0:
                        current_pnl_ticks = (self.entry_price - current_price) / self.tick_size
                    else:
                        logger.warning(f"[EXIT_CHECK] [ERROR] tick_size inválido: {self.tick_size}")
                        return False, ""
        else:
            logger.debug(f"[EXIT_CHECK] [ERROR] No hay datos de mercado (BID/OFFER)")
            return False, ""
        
        # Validar que current_pnl_ticks sea un número válido
        if not isinstance(current_pnl_ticks, (int, float)) or not isinstance(self.tick_size, (int, float)) or self.tick_size <= 0:
            logger.warning(f"[EXIT_CHECK] [ERROR] No se puede calcular P&L: pnl_ticks={current_pnl_ticks}, tick_size={self.tick_size}")
            return False, ""
        
        logger.info(f"[EXIT] P&L actual: {current_pnl_ticks:+.1f} ticks (precio: ${current_price:.2f})")
        logger.info(f"[EXIT] BID: ${bid_price:.2f}, OFFER: ${offer_price:.2f}" if bid_price and offer_price else "[EXIT] BID/OFFER: N/A")
        
        # PRIMERO: Verificar precios fijos (EJECUCIÓN INSTANTÁNEA) - PRIORIDAD MÁXIMA
        # ============================================================================
        if self.fixed_exit_prices:
            reference_price = bid_price if self.entry_side_actual == 'BUY' else offer_price
            if reference_price is not None:
                for exit_config in sorted(self.fixed_exit_prices, key=lambda x: x[0] if isinstance(x, (list, tuple)) else x):
                    exit_price = float(exit_config[0] if isinstance(exit_config, (list, tuple)) else exit_config)
                    exit_qty = exit_config[1] if isinstance(exit_config, (list, tuple)) and len(exit_config) > 1 else None
                    exit_key = f"{exit_price:.2f}"
                    
                    if self.executed_partial_exits.get(exit_key, False):
                        continue
                    
                    price_reached = (reference_price >= exit_price) if self.entry_side_actual == 'BUY' else (reference_price <= exit_price)
                    if price_reached:
                        logger.info(f"[EXIT] [FIXED_PRICE] ALCANZADO: ${exit_price:.2f} (actual: ${reference_price:.2f})")
                        
                        if not exit_qty:  # Cierre completo
                            self.executed_partial_exits[exit_key] = True
                            return True, f"FIXED_PRICE_{exit_price:.2f}_FULL"
                        
                        # Salida parcial
                        if self._execute_partial_exit(exit_price, exit_qty):
                            self.executed_partial_exits[exit_key] = exit_qty
                            logger.info(f"[EXIT] [FIXED_PRICE] Parcial: {exit_qty} @ ${exit_price:.2f}")
                        else:
                            logger.warning(f"[EXIT] [FIXED_PRICE] Error ejecutando parcial")
        
        # Take profit (con gestión de posición basada en tiempo si está habilitada)
        minutes_in_position = (time.time() - self.entry_time) / 60 if self.entry_time else 0
        
        if self.time_based_tp_enabled:
            # Usar TP dinámico (degradación progresiva)
            dynamic_tp, tp_state = self._get_dynamic_tp(minutes_in_position)
            
            logger.info(f"[EXIT] [TIME_BASED_TP] Tiempo en posición: {minutes_in_position:.2f} min")
            logger.info(f"[EXIT] [TIME_BASED_TP] Estado TP: {tp_state} | TP objetivo: {dynamic_tp:+.2f} ticks")
            
            if tp_state == 'STOP_LOSS':
                # Si llegamos al tiempo de stop loss, aplicar SL directamente
                if self.target_stop_loss_ticks and self.target_stop_loss_ticks > 0:
                    if current_pnl_ticks <= -self.target_stop_loss_ticks:
                        logger.warning(f"[EXIT] [OK] STOP_LOSS (time-based) alcanzado: {current_pnl_ticks:+.1f} <= -{self.target_stop_loss_ticks} ticks")
                        logger.info(f"[EXIT] ========== DEBE CERRAR POSICIÓN ==========")
                        return True, "STOP_LOSS_TIME_BASED"
            elif tp_state == 'BREAK_EVEN':
                # Break even: cerrar si P&L >= 0
                if current_pnl_ticks >= 0:
                    logger.info(f"[EXIT] [OK] BREAK_EVEN alcanzado: {current_pnl_ticks:+.1f} >= 0 ticks")
                    logger.info(f"[EXIT] ========== DEBE CERRAR POSICIÓN ==========")
                    return True, "BREAK_EVEN"
                else:
                    logger.info(f"[EXIT] BREAK_EVEN NO alcanzado: {current_pnl_ticks:+.1f} < 0")
            else:
                # TP inicial o degradado
                if dynamic_tp > 0 and current_pnl_ticks >= dynamic_tp:
                    logger.info(f"[EXIT] [OK] TAKE_PROFIT ({tp_state}) alcanzado: {current_pnl_ticks:+.1f} >= +{dynamic_tp:.2f} ticks")
                    logger.info(f"[EXIT] ========== DEBE CERRAR POSICIÓN ==========")
                    return True, f"TAKE_PROFIT_{tp_state}"
                else:
                    logger.info(f"[EXIT] TP ({tp_state}) NO alcanzado: {current_pnl_ticks:+.1f} < {dynamic_tp:.2f}")
        else:
            # TP estándar (sin degradación)
            if self.target_profit_ticks and self.target_profit_ticks > 0:
                logger.info(f"[EXIT] TP objetivo: +{self.target_profit_ticks} ticks")
                logger.info(f"[EXIT] Comparando: P&L {current_pnl_ticks:+.1f} >= TP {self.target_profit_ticks}")
                if current_pnl_ticks >= self.target_profit_ticks:
                    logger.info(f"[EXIT] [OK] TAKE_PROFIT alcanzado: {current_pnl_ticks:+.1f} >= +{self.target_profit_ticks} ticks")
                    logger.info(f"[EXIT] ========== DEBE CERRAR POSICIÓN ==========")
                    return True, "TAKE_PROFIT"
                else:
                    logger.info(f"[EXIT] TP NO alcanzado: {current_pnl_ticks:+.1f} < {self.target_profit_ticks}")
        
        # Stop loss (solo si no está usando gestión basada en tiempo, ya que se maneja allí)
        if not self.time_based_tp_enabled:
            if self.target_stop_loss_ticks and self.target_stop_loss_ticks > 0:
                logger.info(f"[EXIT] SL objetivo: -{self.target_stop_loss_ticks} ticks")
                logger.info(f"[EXIT] Comparando: P&L {current_pnl_ticks:+.1f} <= SL -{self.target_stop_loss_ticks}")
                if current_pnl_ticks <= -self.target_stop_loss_ticks:
                    logger.warning(f"[EXIT] [OK] STOP_LOSS alcanzado: {current_pnl_ticks:+.1f} <= -{self.target_stop_loss_ticks} ticks")
                    logger.info(f"[EXIT] ========== DEBE CERRAR POSICIÓN ==========")
                    return True, "STOP_LOSS"
                else:
                    logger.info(f"[EXIT] SL NO alcanzado: {current_pnl_ticks:+.1f} > -{self.target_stop_loss_ticks}")
        else:
            # En modo time-based, el SL se maneja dentro de la lógica de degradación
            # Solo verificar SL inmediato si se excede el límite antes del tiempo configurado
            if self.target_stop_loss_ticks and self.target_stop_loss_ticks > 0:
                if current_pnl_ticks <= -self.target_stop_loss_ticks:
                    logger.warning(f"[EXIT] [OK] STOP_LOSS inmediato alcanzado: {current_pnl_ticks:+.1f} <= -{self.target_stop_loss_ticks} ticks")
                    logger.info(f"[EXIT] ========== DEBE CERRAR POSICIÓN ==========")
                    return True, "STOP_LOSS_IMMEDIATE"
        
        # Time exit
        if self.target_time_exit_minutes and self.entry_time:
            minutes_in_position = (time.time() - self.entry_time) / 60
            logger.info(f"[EXIT] Tiempo en posición: {minutes_in_position:.1f} min (límite: {self.target_time_exit_minutes} min)")
            logger.info(f"[EXIT] Comparando: {minutes_in_position:.1f} >= {self.target_time_exit_minutes}")
            if minutes_in_position >= self.target_time_exit_minutes:
                logger.info(f"[EXIT] [OK] TIME_EXIT alcanzado: {minutes_in_position:.1f} >= {self.target_time_exit_minutes} min")
                logger.info(f"[EXIT] ========== DEBE CERRAR POSICIÓN ==========")
                return True, "TIME_EXIT"
            else:
                logger.info(f"[EXIT] TIME_EXIT NO alcanzado: {minutes_in_position:.1f} < {self.target_time_exit_minutes}")
        
        logger.info(f"[EXIT] [INFO] Ninguna condición de salida cumplida - manteniendo posición")
        logger.info(f"[EXIT] ========================================")
        return False, ""
    
    def place_order(self, side: str, price: float, quantity: int, order_role: str = 'ENTRY') -> Optional[Dict]:
        """
        Enviar orden según documentación Primary API (páginas 696-775)
        
        Parámetros obligatorios según manual:
        - marketId: ROFX (pyRofex lo maneja)
        - symbol: símbolo del instrumento
        - side: BUY o SELL
        - price: precio de la orden
        - orderQty: cantidad
        - ordType: LIMIT o MARKET
        - timeInForce: DAY, IOC, FOK, GTD
        - account: número de cuenta (OBLIGATORIO - página 746)
        """
        logger.info("="*70)
        logger.info(f"[ENVIAR ORDEN] {side} {quantity} contrato(s) @ ${price:.2f} | rol={order_role}")
        logger.info(f"   Estado: {len(self.active_orders)} orden(es) activa(s), {len(self.order_cancel_pending)} cancelación(es) pendiente(s)")
        logger.info("="*70)
        
        # Verificación adicional en place_order (última línea de defensa)
        # NOTA: NO verificamos _order_lock aquí porque es esperado que esté activo
        # cuando se llama desde open_position() o close_position() (ellos lo activan)
        if self.active_order or len(self.active_orders) > 0:
            logger.error(f"[ERROR] No se puede enviar orden: Ya hay {len(self.active_orders)} orden(es) activa(s)")
            if self.active_order:
                logger.error(f"   Orden activa: {self.active_order}")
            if self.active_orders:
                for oid in list(self.active_orders.keys())[:3]:  # Mostrar máximo 3
                    state = self.order_states.get(oid, 'UNKNOWN')
                    logger.error(f"   - {oid}: {state}")
            return None
        
        if len(self.order_cancel_pending) > 0:
            logger.error(f"[ERROR] No se puede enviar orden: Esperando confirmación de {len(self.order_cancel_pending)} cancelación(es)")
            logger.error(f"   Órdenes pendientes: {list(self.order_cancel_pending)[:5]}")  # Mostrar máximo 5
            return None
        
        try:
            price_str = f"${price:.2f}" if price else "MKT"
            logger.info(f"[PREPARANDO] {self.future_symbol} | {side} | {quantity}@{price_str} | {self.order_type} | {self.time_in_force}")
            
            # Validar parámetros
            if self.order_type == 'LIMIT':
                if price is None or price <= 0:
                    logger.error(f"[ERROR] Precio inválido para orden LIMIT: ${price}")
                    return None
            
            if quantity <= 0:
                logger.error(f"[ERROR] Cantidad inválida: {quantity} (debe ser > 0)")
                return None
            
            # Convertir order_type a pyRofex enum
            order_type_map = {
                'LIMIT': pyRofex.OrderType.LIMIT,
                'MARKET': pyRofex.OrderType.MARKET,
            }
            py_order_type = order_type_map.get(self.order_type, pyRofex.OrderType.LIMIT)
            
            # Convertir TimeInForce a pyRofex enum
            # Valores del enum según pyRofex: DAY, ImmediateOrCancel, FillOrKill, GoodTillDate
            tif_map = {
                'DAY': pyRofex.TimeInForce.DAY,
                'IOC': pyRofex.TimeInForce.ImmediateOrCancel,
                'FOK': pyRofex.TimeInForce.FillOrKill,
                'GTD': pyRofex.TimeInForce.GoodTillDate,
            }
            py_time_in_force = tif_map.get(self.time_in_force, pyRofex.TimeInForce.DAY)
            
            # Preparar parámetros para enviar orden según Primary API
            send_kwargs = dict(
                ticker=self.future_symbol,
                side=pyRofex.Side.BUY if side == 'BUY' else pyRofex.Side.SELL,
                size=quantity,
                order_type=py_order_type,
                time_in_force=py_time_in_force
            )
            if self.order_type == 'LIMIT':
                send_kwargs['price'] = price
            
            # Verificación final antes de enviar a la API
            if len(self.active_orders) > 0 or len(self.order_cancel_pending) > 0:
                logger.error(f"[ERROR CRÍTICO] Estado inconsistente antes de enviar - ABORTANDO")
                logger.error(f"   active_orders: {len(self.active_orders)}, cancel_pending: {len(self.order_cancel_pending)}")
                return None
            
            # Enviar orden con reintentos automáticos
            order = None
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    if attempt > 0:
                        logger.info(f"[REINTENTO] Intento {attempt+1}/{max_retries}...")
                    else:
                        logger.info(f"[ENVIANDO] Conectando con API de ROFEX...")
                    
                    order = pyRofex.send_order(**send_kwargs)
                    logger.info(f"[OK] Orden recibida por la API")
                    break  # Éxito, salir del loop
                    
                except TimeoutError as te:
                    logger.warning(f"[TIMEOUT] Intento {attempt+1}/{max_retries}: {te}")
                    if attempt < max_retries - 1:
                        time.sleep(1)
                        logger.info(f"[ESPERANDO] Reintentando en 1 segundo...")
                    else:
                        logger.error(f"[ERROR] Timeout después de {max_retries} intentos - orden no enviada")
                        raise
                        
                except (ConnectionError, OSError) as ie:
                    logger.warning(f"[ERROR RED] Intento {attempt+1}/{max_retries}: {ie}")
                    if attempt < max_retries - 1:
                        time.sleep(2)
                        logger.info(f"[ESPERANDO] Reintentando en 2 segundos...")
                    else:
                        logger.error(f"[ERROR] Error de conexión después de {max_retries} intentos")
                        raise
                        
                except Exception as e:
                    logger.error(f"[ERROR] Error inesperado: {e}")
                    raise
            
            # Procesar respuesta de la API
            if not order:
                logger.error(f"[ERROR] No se recibió respuesta de la API")
                return None
            
            if order.get('status') == 'OK':
                order_info = order.get('order', {})
                cl_ord_id = order_info.get('clientId')
                proprietary = order_info.get('proprietary', 'api')
                
                # Validar que recibimos clientId (crítico)
                if not cl_ord_id:
                    logger.error(f"[ERROR] La API no devolvió clientId - orden no puede ser rastreada")
                    logger.error(f"   Respuesta: {order}")
                    return None
                
                logger.info(f"[OK] Orden aceptada por API | ID: {cl_ord_id}")
                
                # CRÍTICO: Actualizar self.proprietary desde la respuesta de la API
                # según manual Primary API, proprietary puede venir en la respuesta y debe usarse para cancel_order
                if proprietary and proprietary != 'api':
                    logger.info(f"[INFO] Actualizando proprietary desde respuesta: {proprietary}")
                    self.proprietary = proprietary
                elif not self.proprietary:
                    # Si no viene en respuesta y no tenemos uno guardado, usar el default
                    self.proprietary = proprietary or 'api'
                    logger.info(f"[INFO] Usando proprietary por defecto: {self.proprietary}")
                
                # Marcar como mejorada si es PRICE_IMPROVEMENT y está permitido
                is_improved = False
                if self.trigger_type == "PRICE_IMPROVEMENT" and self.allow_price_improvement_once:
                    self.orders_price_improved.add(cl_ord_id)
                    is_improved = True
                    logger.info(f"[INFO] Orden {cl_ord_id} marcada como mejorada (solo se mejorará una vez)")
                
                # Almacenar orden en estado interno
                self.active_orders[cl_ord_id] = {
                    'symbol': self.future_symbol,
                    'side': side,
                    'price': price,
                    'quantity': quantity,
                    'original_quantity': quantity,
                    'filled_quantity': 0,
                    'remaining_quantity': quantity,
                    'avg_price': None,
                    'timestamp': time.time(),
                    'order_info': order_info,
                    'proprietary': self.proprietary,
                    'price_improved': is_improved,
                    'role': order_role
                }
                self.order_states[cl_ord_id] = 'PENDING_NEW'
                self.active_order = cl_ord_id
                
                logger.info(f"[ALMACENADA] Orden registrada | Estado: PENDING_NEW")
                logger.info(f"   Detalles: {side} {quantity}@${price:.2f}")
                
                # No registrar en CSV hasta estado final (optimización para reducir filas redundantes)
                
                logger.info(f"[ESPERANDO] Confirmación del mercado (ExecutionReport vía WebSocket)...")
                return order
            else:
                # Orden rechazada por la API
                status = order.get('status', 'UNKNOWN')
                message = order.get('message', 'Sin mensaje')
                description = order.get('description', 'Sin descripción')
                
                logger.error(f"[RECHAZADA] La API rechazó la orden")
                logger.error(f"   Status: {status}")
                if message:
                    logger.error(f"   Mensaje: {message}")
                if description:
                    logger.error(f"   Descripción: {description}")
                
                # Sugerencias para errores comunes
                desc_lower = description.lower()
                if 'cuenta' in desc_lower or 'account' in desc_lower:
                    logger.error(f"   [SUGERENCIA] Verificar configuración de cuenta en .env")
                elif 'precio' in desc_lower or 'price' in desc_lower:
                    logger.error(f"   [SUGERENCIA] Verificar que el precio esté dentro del rango válido")
                elif 'cantidad' in desc_lower or 'quantity' in desc_lower or 'size' in desc_lower:
                    logger.error(f"   [SUGERENCIA] Verificar que la cantidad sea válida")
                
                return None
                
        except Exception as e:
            logger.error(f"[ERROR] Error enviando orden: {e}")
            import traceback
            logger.error(f"[ERROR] Traceback completo:\n{traceback.format_exc()}")
            return None
    
    def cancel_order(self, cl_ord_id: str) -> bool:
        """
        Cancelar orden según documentación Primary API
        
        Requiere (según manual Primary-API.pdf página 26):
        - clOrdId: El ID del request devuelto al ingresar la orden
        - proprietary: ID del participante (campo obligatorio)
        """
        logger.info(f"[FUNC_CALL] [CANCEL] cancel_order() LLAMADO para clOrdId={cl_ord_id}")
        try:
            # Verificar que la orden existe en nuestro tracking
            if cl_ord_id not in self.active_orders:
                logger.warning(f"[WARNING] Orden {cl_ord_id} no existe en active_orders")
                # Limpiar flags si existen
                if cl_ord_id in self.order_cancel_pending:
                    self.order_cancel_pending.discard(cl_ord_id)
                if cl_ord_id in self.orders_price_improved:
                    self.orders_price_improved.discard(cl_ord_id)
                return False
            
            order_info = self.active_orders[cl_ord_id]
            current_state = self.order_states.get(cl_ord_id, 'UNKNOWN')
            
            # CRÍTICO: No cancelar órdenes en estados terminales
            if current_state in ['FILLED', 'CANCELLED', 'REJECTED']:
                logger.warning(f"[CANCEL] [WARNING] Orden {cl_ord_id} ya está en estado terminal ({current_state}), no se puede cancelar")
                logger.warning(f"[CANCEL] Limpiando orden de tracking...")
                # Limpiar orden en estado terminal
                if cl_ord_id in self.orders_price_improved:
                    self.orders_price_improved.discard(cl_ord_id)
                if cl_ord_id in self.order_cancel_pending:
                    self.order_cancel_pending.discard(cl_ord_id)
                del self.active_orders[cl_ord_id]
                if cl_ord_id in self.order_states:
                    del self.order_states[cl_ord_id]
                if self.active_order == cl_ord_id:
                    self.active_order = None
                return True  # Retornar True porque la orden fue limpiada
            
            # CRÍTICO: Verificar si ya está pendiente de cancelación
            if cl_ord_id in self.order_cancel_pending:
                cancel_ts = order_info.get('cancel_ts', 0)
                attempts = order_info.get('cancel_attempts', 0)
                logger.info(f"[CANCEL] Orden {cl_ord_id} ya está pendiente de cancelación (intentos: {attempts})")
                # Si ya pasó tiempo suficiente, permitir reintento
                if time.time() - cancel_ts < 3:
                    logger.info(f"[CANCEL] Cancelación aún pendiente (hace {time.time() - cancel_ts:.1f}s), no reintentando")
                    return True  # Retornar True porque ya está en proceso
            
            # CASO 4: Obtener estado actual de la orden antes de cancelar (para validar LeavesQty y CumQty)
            leaves_qty = None
            cum_qty = None
            original_qty = order_info.get('quantity', 0)
            
            # Obtener estado actual de la orden antes de cancelar
            try:
                order_status = pyRofex.get_order_status(client_order_id=cl_ord_id)
                if order_status and isinstance(order_status, dict):
                    # Extraer LeavesQty y CumQty de la respuesta
                    if 'order' in order_status:
                        order_data = order_status['order']
                        leaves_qty = order_data.get('leavesQty') or order_data.get('leavesQuantity') or order_data.get('remainingQty')
                        cum_qty = order_data.get('cumQty') or order_data.get('cumQuantity') or order_data.get('filledQty')
                    else:
                        leaves_qty = order_status.get('leavesQty') or order_status.get('leavesQuantity')
                        cum_qty = order_status.get('cumQty') or order_status.get('cumQuantity')
            except Exception as status_error:
                logger.debug(f"[CANCEL] No se pudo obtener estado antes de cancelar: {status_error}")
            
            logger.info(f"[CANCEL] Cancelando orden: {cl_ord_id}")
            logger.info(f"   - Side: {order_info['side']}")
            logger.info(f"   - Price: ${order_info['price']}")
            logger.info(f"   - Quantity: {order_info['quantity']}")
            logger.info(f"   - Estado actual: {current_state}")
            
            # CASO 4: Mostrar información de cantidad antes de cancelar
            if leaves_qty is not None and cum_qty is not None:
                logger.info(f"[CANCEL] ORDEN {cl_ord_id} antes de cancelar:")
                logger.info(f"   - Cantidad original: {original_qty}")
                logger.info(f"   - Cantidad ejecutada (CumQty): {cum_qty}")
                logger.info(f"   - Cantidad remanente (LeavesQty): {leaves_qty}")
                logger.info(f"   - Validación: {cum_qty} + {leaves_qty} = {cum_qty + leaves_qty} (debe ser {original_qty})")
                
                # Validar que CumQty + LeavesQty = cantidad original
                if abs((cum_qty + leaves_qty) - original_qty) > 0.01:
                    logger.warning(f"[CANCEL] ADVERTENCIA: Suma de CumQty y LeavesQty no coincide con cantidad original")
            
            # Según manual Primary API: requiere clOrdId (clientId) y proprietary
            # pyRofex.cancel_order() acepta clientId y proprietary como parámetros directos
            # CRÍTICO: Usar proprietary desde la orden guardada, no el global
            proprietary_to_use = order_info.get('proprietary', self.proprietary)
            if not proprietary_to_use:
                proprietary_to_use = self.proprietary or 'api'
            
            logger.info(f"[CANCEL] Usando proprietary: {proprietary_to_use} (de orden guardada: {order_info.get('proprietary', 'N/A')})")
            
            max_retries = 3
            
            for attempt in range(max_retries):
                try:
                    # Llamar con parámetros directos según manual Primary API
                    # Según documentación: cancel_order(client_order_id, proprietary)
                    resp = pyRofex.cancel_order(client_order_id=cl_ord_id, proprietary=proprietary_to_use)
                    logger.info(f"[OK] Cancel request enviada para clOrdId={cl_ord_id} | resp={resp}")
                    
                    # Verificar si la respuesta indica que la orden no existe
                    if resp and isinstance(resp, dict):
                        resp_status = resp.get('status', '').upper()
                        resp_description = str(resp.get('description', '')).lower()
                        
                        # Si la orden no existe, limpiarla automáticamente
                        if resp_status == 'ERROR' or 'doesn\'t exist' in resp_description or 'does not exist' in resp_description or 'not exist' in resp_description:
                            logger.warning(f"[CANCEL] [WARNING] Orden {cl_ord_id} no existe en el exchange")
                            logger.warning(f"[CANCEL] Respuesta: {resp}")
                            logger.warning(f"[CANCEL] Acción: Limpiando orden automáticamente de active_orders")
                            
                            # Limpiar orden que no existe
                            if cl_ord_id in self.active_orders:
                                # Limpiar flags
                                if cl_ord_id in self.orders_price_improved:
                                    self.orders_price_improved.discard(cl_ord_id)
                                if cl_ord_id in self.order_cancel_pending:
                                    self.order_cancel_pending.discard(cl_ord_id)
                                
                                # Registrar en CSV como CANCELLED (aunque no se canceló realmente, ya no existe)
                                self._log_order_to_csv(
                                    cl_ord_id,
                                    self.active_orders[cl_ord_id]['side'],
                                    self.active_orders[cl_ord_id]['price'],
                                    self.active_orders[cl_ord_id]['quantity'],
                                    'CANCELLED'  # Marcar como cancelada aunque fue rechazada/eliminada
                                )
                                
                                del self.active_orders[cl_ord_id]
                                if cl_ord_id in self.order_states:
                                    del self.order_states[cl_ord_id]
                                if self.active_order == cl_ord_id:
                                    self.active_order = None
                                logger.info(f"[CANCEL] [OK] Orden {cl_ord_id} limpiada (no existía en exchange)")
                            
                            return True  # Retornar True porque la orden fue "limpiada" exitosamente
                    
                    # Si la respuesta es OK o no indica error, marcar como pendiente
                    # CRÍTICO: Solo marcar como pendiente si no estaba ya en estado terminal
                    if current_state not in ['FILLED', 'CANCELLED', 'REJECTED']:
                        self.order_cancel_pending.add(cl_ord_id)
                        order_info['cancel_ts'] = time.time()
                        order_info['cancel_attempts'] = order_info.get('cancel_attempts', 0) + 1
                        logger.info(f"[CANCEL] Orden {cl_ord_id} marcada como pendiente de cancelación (intento {order_info['cancel_attempts']})")
                    else:
                        logger.warning(f"[CANCEL] [WARNING] Orden {cl_ord_id} cambió a estado terminal ({current_state}) antes de marcar como pendiente")
                        # Limpiar de tracking
                        if cl_ord_id in self.active_orders:
                            if cl_ord_id in self.orders_price_improved:
                                self.orders_price_improved.discard(cl_ord_id)
                            if cl_ord_id in self.order_cancel_pending:
                                self.order_cancel_pending.discard(cl_ord_id)
                            del self.active_orders[cl_ord_id]
                            if cl_ord_id in self.order_states:
                                del self.order_states[cl_ord_id]
                            if self.active_order == cl_ord_id:
                                self.active_order = None
                    return True
                except TimeoutError as te:
                    logger.warning(f"[WARNING] Timeout en cancel_order (intento {attempt+1}/{max_retries}): {te}")
                    if attempt < max_retries - 1:
                        time.sleep(1)
                    else:
                        logger.error(f"[ERROR] Timeout después de {max_retries} intentos")
                        return False
                except (ConnectionError, OSError) as ie:
                    logger.warning(f"[WARNING] Error de I/O en cancel_order (intento {attempt+1}/{max_retries}): {ie}")
                    if attempt < max_retries - 1:
                        time.sleep(2)
                    else:
                        logger.error(f"[ERROR] Error de I/O después de {max_retries} intentos")
                        return False
                except Exception as e1:
                    error_str = str(e1).lower()
                    
                    # Caso 4.1: Client Order ID incorrecto - manejo específico
                    if 'invalid' in error_str or 'not found' in error_str or "doesn't exist" in error_str or 'order id' in error_str:
                        logger.error(f"[ERROR] Client Order ID incorrecto para orden {cl_ord_id}: {e1}")
                        logger.warning(f"[CANCEL] Limpiando orden inválida del registro local")
                        # Limpiar orden inválida del registro local
                        if cl_ord_id in self.active_orders:
                            del self.active_orders[cl_ord_id]
                        if cl_ord_id in self.order_states:
                            del self.order_states[cl_ord_id]
                        if cl_ord_id in self.order_cancel_pending:
                            self.order_cancel_pending.discard(cl_ord_id)
                        return False
                    else:
                        logger.error(f"[ERROR] Cancelación falló para {cl_ord_id}: {e1}")
                        return False
            
        except Exception as e:
            error_str = str(e).lower()
            
            # Caso 4.1: Client Order ID incorrecto - manejo específico
            if 'invalid' in error_str or 'not found' in error_str or "doesn't exist" in error_str or 'order id' in error_str:
                logger.error(f"[ERROR] Client Order ID incorrecto para orden {cl_ord_id}: {e}")
                logger.warning(f"[CANCEL] Limpiando orden inválida del registro local")
                # Limpiar orden inválida del registro local
                if cl_ord_id in self.active_orders:
                    del self.active_orders[cl_ord_id]
                if cl_ord_id in self.order_states:
                    del self.order_states[cl_ord_id]
                if cl_ord_id in self.order_cancel_pending:
                    self.order_cancel_pending.discard(cl_ord_id)
                return False
            else:
                logger.error(f"[ERROR] Error cancelando orden {cl_ord_id}: {e}")
                import traceback
                logger.error(traceback.format_exc())
                return False
    
    def check_order_timeout(self):
        """Verificar timeout de órdenes y cancelarlas si es necesario"""
        # Logging throttled - solo cada 10 segundos
        if not hasattr(self, '_last_timeout_check_log'):
            self._last_timeout_check_log = 0
        
        now = time.time()
        should_log = (now - self._last_timeout_check_log) >= 10
        
        if should_log and self.active_orders:
            logger.debug(f"[FUNC_CALL] [TIMEOUT] check_order_timeout() LLAMADO - {len(self.active_orders)} orden(es) activa(s)")
            self._last_timeout_check_log = now
        
        if not self.active_orders:
            return
        
        now = time.time()
        orders_to_cancel = []
        
        for cl_ord_id, order_info in list(self.active_orders.items()):
            # Validar que timestamp existe y es válido
            if 'timestamp' not in order_info:
                logger.warning(f"[WARNING] Orden {cl_ord_id} no tiene timestamp, usando tiempo actual")
                order_info['timestamp'] = now
                order_age = 0
            else:
                timestamp = order_info['timestamp']
                if not isinstance(timestamp, (int, float)) or timestamp <= 0:
                    logger.warning(f"[WARNING] Timestamp inválido para orden {cl_ord_id}: {timestamp}")
                    order_info['timestamp'] = now
                    order_age = 0
                else:
                    order_age = now - timestamp
            
            state = self.order_states.get(cl_ord_id, 'UNKNOWN')
            
            # Solo cancelar órdenes que NO están en estados finales
            terminal_states = ['FILLED', 'CANCELLED', 'REJECTED']
            
            if order_age > self.order_timeout_seconds and state not in terminal_states:
                logger.warning(f"[TIMEOUT] [TIMEOUT] Orden {cl_ord_id} EXCEDE TIMEOUT:")
                logger.warning(f"   - Estado actual: {state}")
                logger.warning(f"   - Tiempo transcurrido: {order_age:.1f}s > {self.order_timeout_seconds}s")
                logger.warning(f"   - Side: {order_info['side']} | Price: ${order_info['price']:.2f} | Qty: {order_info['quantity']}")
                logger.warning(f"[TIMEOUT] Acción: Agregando a lista para cancelación inmediata")
                orders_to_cancel.append(cl_ord_id)

            # Reintentos de cancelación si quedó pendiente y ya pasó 3s
            # CRÍTICO: Solo reintentar si la orden aún existe y no está en estado terminal
            if cl_ord_id in self.order_cancel_pending and cl_ord_id in self.active_orders:
                cancel_ts = order_info.get('cancel_ts', 0)
                attempts = order_info.get('cancel_attempts', 0)
                
                # Verificar estado antes de reintentar
                if state in terminal_states:
                    logger.info(f"[TIMEOUT] Orden {cl_ord_id} en estado terminal ({state}), limpiando flag de cancelación pendiente")
                    self.order_cancel_pending.discard(cl_ord_id)
                elif now - cancel_ts >= 3 and attempts < 3:
                    logger.info(f"[CANCEL-RETRY] Reintentando cancelación de {cl_ord_id} (intento {attempts+1})")
                    self.cancel_order(cl_ord_id)
                elif attempts >= 3:
                    # Consultar estado por API y decidir limpieza
                    try:
                        # CRÍTICO: Usar proprietary desde la orden guardada
                        proprietary_to_use = self.active_orders[cl_ord_id].get('proprietary', self.proprietary) if cl_ord_id in self.active_orders else self.proprietary
                        if not proprietary_to_use:
                            proprietary_to_use = 'api'
                        status_resp = pyRofex.get_order_status(client_order_id=cl_ord_id, proprietary=proprietary_to_use)
                        logger.info(f"[STATUS] Estado post-cancel {cl_ord_id}: {status_resp}")
                        
                        # CRÍTICO: Procesar respuesta de get_order_status
                        if status_resp and isinstance(status_resp, dict):
                            resp_status = status_resp.get('status', '').upper()
                            resp_description = str(status_resp.get('description', '')).lower()
                            order_data = status_resp.get('order', {})
                            order_status_from_api = order_data.get('status', '').upper() if isinstance(order_data, dict) else ''
                            
                            # CRÍTICO: Si la orden está FILLED según API pero estado interno es PENDING_NEW
                            if resp_status == 'OK' and order_status_from_api == 'FILLED':
                                logger.error(f"[STATUS] [CRÍTICO] Orden {cl_ord_id} está FILLED según API pero estado interno es {state}")
                                logger.error(f"[STATUS] La orden fue ejecutada pero no se recibió ExecutionReport - procesando manualmente...")
                                
                                # Construir order_report simulado para procesar como ExecutionReport
                                simulated_order_report = {
                                    'clOrdId': cl_ord_id,
                                    'orderId': order_data.get('orderId', ''),
                                    'status': 'FILLED',
                                    'avgPx': order_data.get('avgPx', 0) or order_data.get('lastPx', 0) or (self.active_orders[cl_ord_id]['price'] if cl_ord_id in self.active_orders else 0),
                                    'cumQty': order_data.get('cumQty', order_data.get('orderQty', (self.active_orders[cl_ord_id]['quantity'] if cl_ord_id in self.active_orders else 0))),
                                    'lastPx': order_data.get('lastPx', 0),
                                    'lastQty': order_data.get('lastQty', 0),
                                    'text': order_data.get('text', 'Ejecutada - detectada por consulta de estado')
                                }
                                
                                # Simular mensaje WebSocket para procesar como ExecutionReport
                                simulated_message = {
                                    'type': 'OR',
                                    'orderReport': simulated_order_report
                                }
                                
                                # CRÍTICO: Verificar que la orden aún existe antes de procesar
                                if cl_ord_id not in self.active_orders:
                                    logger.warning(f"[STATUS] [WARNING] Orden {cl_ord_id} ya no está en active_orders, no procesando FILLED")
                                    continue
                                
                                # Procesar FILLED como si fuera un ExecutionReport recibido
                                try:
                                    logger.info(f"[STATUS] Procesando orden {cl_ord_id} como FILLED...")
                                    self._order_report_handler(simulated_message)
                                    logger.info(f"[STATUS] [OK] Orden {cl_ord_id} procesada exitosamente como FILLED")
                                except Exception as e:
                                    logger.error(f"[STATUS] [ERROR] Error procesando orden FILLED: {e}")
                                    import traceback
                                    traceback.print_exc()
                                
                                # Salir del loop de timeout para esta orden ya que fue procesada
                                continue
                                
                            elif resp_status == 'ERROR' or 'doesn\'t exist' in resp_description or 'does not exist' in resp_description or 'not exist' in resp_description:
                                logger.warning(f"[STATUS] [WARNING] Orden {cl_ord_id} no existe en el exchange")
                                logger.warning(f"[STATUS] Limpiando orden automáticamente...")
                                
                                # Limpiar orden que no existe
                                if cl_ord_id in self.active_orders:
                                    if cl_ord_id in self.orders_price_improved:
                                        self.orders_price_improved.discard(cl_ord_id)
                                    if cl_ord_id in self.order_cancel_pending:
                                        self.order_cancel_pending.discard(cl_ord_id)
                                    
                                    self._log_order_to_csv(
                                        cl_ord_id,
                                        self.active_orders[cl_ord_id]['side'],
                                        self.active_orders[cl_ord_id]['price'],
                                        self.active_orders[cl_ord_id]['quantity'],
                                        'CANCELLED'
                                    )
                                    
                                    del self.active_orders[cl_ord_id]
                                    if cl_ord_id in self.order_states:
                                        del self.order_states[cl_ord_id]
                                    if self.active_order == cl_ord_id:
                                        self.active_order = None
                                    logger.info(f"[STATUS] [OK] Orden {cl_ord_id} limpiada (no existía en exchange)")
                            else:
                                # Actualizar estado si viene en la respuesta
                                if order_status_from_api and order_status_from_api in ['FILLED', 'CANCELLED', 'REJECTED', 'NEW', 'PENDING_NEW']:
                                    logger.info(f"[STATUS] Actualizando estado de {cl_ord_id}: {state} -> {order_status_from_api}")
                                    self.order_states[cl_ord_id] = order_status_from_api
                                    
                                    # Si está en estado terminal, limpiar flags
                                    if order_status_from_api in ['FILLED', 'CANCELLED', 'REJECTED']:
                                        if cl_ord_id in self.order_cancel_pending:
                                            self.order_cancel_pending.discard(cl_ord_id)
                                            logger.info(f"[STATUS] Limpiado flag de cancelación para {cl_ord_id}")
                                        
                                        # Si está FILLED pero no se procesó arriba, procesarla
                                        # CRÍTICO: Solo procesar si la orden aún existe en active_orders
                                        if order_status_from_api == 'FILLED' and cl_ord_id in self.active_orders:
                                            current_state_check = self.order_states.get(cl_ord_id, 'UNKNOWN')
                                            # Solo procesar si aún no está en estado terminal
                                            if current_state_check not in ['FILLED', 'CANCELLED', 'REJECTED']:
                                                logger.warning(f"[STATUS] [WARNING] Orden {cl_ord_id} FILLED pero no se procesó arriba - procesando ahora...")
                                                try:
                                                    simulated_order_report = {
                                                        'clOrdId': cl_ord_id,
                                                        'orderId': order_data.get('orderId', ''),
                                                        'status': 'FILLED',
                                                        'avgPx': order_data.get('avgPx', 0) or order_data.get('lastPx', 0) or self.active_orders[cl_ord_id]['price'],
                                                        'cumQty': order_data.get('cumQty', self.active_orders[cl_ord_id]['quantity']),
                                                        'lastPx': order_data.get('lastPx', 0),
                                                        'lastQty': order_data.get('lastQty', 0),
                                                        'text': order_data.get('text', 'Ejecutada')
                                                    }
                                                    simulated_message = {'type': 'OR', 'orderReport': simulated_order_report}
                                                    self._order_report_handler(simulated_message)
                                                except Exception as e:
                                                    logger.error(f"[STATUS] Error procesando FILLED en else: {e}")
                                            else:
                                                logger.info(f"[STATUS] Orden {cl_ord_id} ya está en estado terminal ({current_state_check}), no procesando nuevamente")
                                                # Limpiar flags
                                                if cl_ord_id in self.order_cancel_pending:
                                                    self.order_cancel_pending.discard(cl_ord_id)
                                                if cl_ord_id in self.orders_price_improved:
                                                    self.orders_price_improved.discard(cl_ord_id)
                    except Exception as e:
                        logger.warning(f"[STATUS] No se pudo consultar estado de {cl_ord_id}: {e}")
        
        # Cancelar todas las órdenes en timeout
        if orders_to_cancel:
            logger.warning(f"[TIMEOUT] Procesando {len(orders_to_cancel)} orden(es) en timeout...")
            
        for cl_ord_id in orders_to_cancel:
            # CRÍTICO: Verificar que la orden aún existe y no está en estado terminal
            if cl_ord_id not in self.active_orders:
                logger.warning(f"[TIMEOUT] [WARNING] Orden {cl_ord_id} ya no está en active_orders, saltando")
                continue
            
            current_state = self.order_states.get(cl_ord_id, 'UNKNOWN')
            if current_state in ['FILLED', 'CANCELLED', 'REJECTED']:
                logger.warning(f"[TIMEOUT] [WARNING] Orden {cl_ord_id} ya está en estado terminal ({current_state}), limpiando y saltando")
                # Limpiar orden en estado terminal
                if cl_ord_id in self.active_orders:
                    if cl_ord_id in self.orders_price_improved:
                        self.orders_price_improved.discard(cl_ord_id)
                    if cl_ord_id in self.order_cancel_pending:
                        self.order_cancel_pending.discard(cl_ord_id)
                    del self.active_orders[cl_ord_id]
                    if cl_ord_id in self.order_states:
                        del self.order_states[cl_ord_id]
                    if self.active_order == cl_ord_id:
                        self.active_order = None
                continue
            
            # CRÍTICO: Verificar si ya está pendiente de cancelación para evitar múltiples intentos
            if cl_ord_id in self.order_cancel_pending:
                logger.info(f"[TIMEOUT] Orden {cl_ord_id} ya está pendiente de cancelación, no reintentando")
                continue
            
            logger.info(f"[TIMEOUT] Intentando cancelar orden {cl_ord_id}...")
            success = self.cancel_order(cl_ord_id)
            if success:
                logger.info(f"[TIMEOUT] [OK] Solicitud de cancelación enviada para {cl_ord_id}")
                logger.info(f"[TIMEOUT] Esperando confirmación CANCELLED del mercado...")
            else:
                logger.error(f"[TIMEOUT] [ERROR] No se pudo enviar cancelación para {cl_ord_id}")
                logger.error(f"[TIMEOUT] Acción: Limpiando orden forzadamente de active_orders")
                # Limpiar forzosamente si no se pudo cancelar
                if cl_ord_id in self.active_orders:
                    if cl_ord_id in self.orders_price_improved:
                        self.orders_price_improved.discard(cl_ord_id)
                    if cl_ord_id in self.order_cancel_pending:
                        self.order_cancel_pending.discard(cl_ord_id)
                    del self.active_orders[cl_ord_id]
                    if cl_ord_id in self.order_states:
                        del self.order_states[cl_ord_id]
                    if self.active_order == cl_ord_id:
                        self.active_order = None
                    logger.warning(f"[TIMEOUT] [OK] Orden {cl_ord_id} limpiada forzadamente")
    
    def open_position(self, quantity_override: Optional[int] = None, allow_existing_position: bool = False):
        """Abre posición o completa la cantidad pendiente de entrada."""
        logger.info(f"[FUNC_CALL] [OPEN] open_position() LLAMADO")
        logger.info("="*70)
        try:
            logger.info(f"[DEBUG] open_position() LLAMADO - Verificando condiciones...")
            logger.info(f"   - active_order: {self.active_order}")
            logger.info(f"   - position_opened: {self.position_opened}")
            logger.info(f"   - is_calibration_complete: {self.is_calibration_complete}")
            logger.info(f"   - enable_latency_filter: {self.enable_latency_filter}")
            logger.info(f"   - quantity_override: {quantity_override}")
            logger.info(f"   - allow_existing_position: {allow_existing_position}")
            
            # CRÍTICO: Verificar lock de envío (previene múltiples llamadas simultáneas)
            if self._order_lock:
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Orden lock activo - otra orden está siendo procesada")
                logger.warning(f"[DEBUG] Tiempo desde último intento: {time.time() - self._last_order_send_attempt:.1f}s")
                return
            
            # Verificar tiempo mínimo entre intentos de envío (adicional al intervalo entre órdenes)
            now = time.time()
            time_since_last_attempt = now - self._last_order_send_attempt
            if time_since_last_attempt < 1.0:  # Mínimo 1 segundo entre intentos
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Muy poco tiempo desde último intento: {time_since_last_attempt:.2f}s < 1.0s")
                return
            
            # Verificar si ya hay una orden activa O posición abierta
            if self.active_order or len(self.active_orders) > 0:
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Hay orden(es) activa(s): active_order={self.active_order}, active_orders={len(self.active_orders)} - NO abriendo nueva posición")
                logger.warning(f"[DEBUG] Detalles de órdenes activas:")
                for cl_id, o_info in self.active_orders.items():
                    state = self.order_states.get(cl_id, 'UNKNOWN')
                    logger.warning(f"[DEBUG]   - {cl_id}: {o_info.get('side')} @ ${o_info.get('price')} | Estado: {state}")
                return
            
            if not allow_existing_position:
                self.entry_target_quantity = self.order_quantity
            
            # CRÍTICO: Verificar si hay órdenes pendientes de cancelación
            if len(self.order_cancel_pending) > 0:
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Hay {len(self.order_cancel_pending)} orden(es) pendiente(s) de cancelación - ESPERANDO confirmación antes de enviar nueva orden")
                logger.warning(f"[DEBUG] Órdenes pendientes de cancelación: {list(self.order_cancel_pending)}")
                
                # Verificar si alguna orden pendiente de cancelación ya fue cancelada
                for cl_ord_id in list(self.order_cancel_pending):
                    state = self.order_states.get(cl_ord_id, 'UNKNOWN')
                    if state in ['CANCELLED', 'REJECTED', 'FILLED']:
                        # Ya fue cancelada/ejecutada/rechazada, limpiar flag
                        logger.info(f"[DEBUG] Orden {cl_ord_id} ya está en estado {state}, limpiando flag de cancelación pendiente")
                        self.order_cancel_pending.discard(cl_ord_id)
                
                # Si aún hay órdenes pendientes, no permitir nueva orden
                if len(self.order_cancel_pending) > 0:
                    logger.warning(f"[DEBUG] Aún hay {len(self.order_cancel_pending)} orden(es) pendiente(s) de confirmación de cancelación")
                    return
            
            if self.position_opened and not allow_existing_position:
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Ya hay posición abierta - NO abriendo nueva posición")
                logger.warning(f"[DEBUG] Detalles de posición abierta:")
                logger.warning(f"   - entry_price: ${self.entry_price:.2f}" if self.entry_price else "   - entry_price: None")
                logger.warning(f"   - entry_side_actual: {self.entry_side_actual}")
                logger.warning(f"   - entry_time: {self.entry_time}")
                logger.warning(f"[DEBUG] [ERROR] Esta verificación debería haber bloqueado el envío de órdenes anteriores")
                return
            
            # Verificar tiempo mínimo entre órdenes
            now = time.time()
            time_since_last = now - self.last_order_time
            if time_since_last < self.dynamic_order_interval:
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Esperando intervalo mínimo: {time_since_last:.1f}s < {self.dynamic_order_interval}s")
                return
            
            # Verificar condiciones de entrada
            entry_ok = self.check_entry_conditions()
            if not entry_ok:
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Condiciones de entrada NO cumplidas")
                return
            else:
                logger.info(f"[DEBUG] [OK] Condiciones de entrada CUMPLIDAS")
            
            # Verificar filtros
            logger.info(f"[DEBUG] Verificando filtros...")
            filter_ok = self.check_filter_conditions()
            if not filter_ok:
                logger.warning(f"[DEBUG] [ERROR] BLOQUEADO: Filtros NO cumplidos - ORDEN BLOQUEADA")
                return
            else:
                logger.info(f"[DEBUG] [OK] Filtros CUMPLIDOS - Procediendo a enviar orden")
            
            # Determinar precio de ejecución
            logger.info(f"[DEBUG] Ejecutando trigger tipo: {self.trigger_type}")
            price = self.execute_trigger()
            if not price:
                logger.warning("[WARNING] [ERROR] BLOQUEADO: No se pudo determinar precio")
                logger.warning(f"   - trigger_type: {self.trigger_type}")
                logger.warning(f"   - entry_side: {self.entry_side}")
                logger.warning(f"   - BID: {self.market_data.get('bid')}")
                logger.warning(f"   - OFFER: {self.market_data.get('offer')}")
                return
            
            pending_entry_qty = self._get_pending_entry_quantity()
            if quantity_override is not None:
                desired_total_new = max(0, int(round(quantity_override)))
            else:
                desired_total_new = max(0, int(round(self.order_quantity - int(round(self.position_quantity)))))
            quantity_to_send = max(0, desired_total_new - pending_entry_qty)
            
            if quantity_to_send <= 0:
                logger.info(f"[DEBUG] [ENTRY] No hay cantidad pendiente para enviar (pendiente={pending_entry_qty}, override={quantity_override})")
                return
            
            logger.info(f"[DEBUG] Cantidad a enviar calculada: {quantity_to_send} (pendiente activo: {pending_entry_qty})")
            
            # Validación final del precio antes de enviar
            if not isinstance(price, (int, float)) or price <= 0:
                logger.error(f"[ERROR] Precio inválido antes de enviar orden: {price}")
                return
            
            logger.info(f"[DEBUG] Precio determinado para orden {self.entry_side}: ${price:.2f}")
            
            # VERIFICACIÓN FINAL ANTES DE ENVIAR (doble check)
            logger.info(f"[DEBUG] VERIFICACIÓN FINAL antes de enviar orden:")
            logger.info(f"   - active_order: {self.active_order}")
            logger.info(f"   - active_orders count: {len(self.active_orders)}")
            logger.info(f"   - order_cancel_pending count: {len(self.order_cancel_pending)}")
            logger.info(f"   - _order_lock: {self._order_lock}")
            logger.info(f"   - position_opened: {self.position_opened}")
            
            # Doble verificación antes de enviar
            if self.active_order or len(self.active_orders) > 0:
                logger.error(f"[OPEN] [ERROR] DOBLE CHECK FALLIDO: Hay órdenes activas justo antes de enviar - ABORTANDO")
                return
            
            if len(self.order_cancel_pending) > 0:
                logger.error(f"[OPEN] [ERROR] DOBLE CHECK FALLIDO: Hay cancelaciones pendientes justo antes de enviar - ABORTANDO")
                return
            
            if self._order_lock:
                logger.error(f"[OPEN] [ERROR] DOBLE CHECK FALLIDO: Lock activo justo antes de enviar - ABORTANDO")
                return
            
            # ACTIVAR LOCK antes de enviar
            self._order_lock = True
            self._last_order_send_attempt = now
            logger.info(f"[DEBUG] [LOCK] Lock de orden ACTIVADO - previene múltiples envíos")
            
            try:
                # Enviar orden LIMIT
                logger.info(f"[OPEN] [OK] ABRIENDO POSICION: {self.entry_side} {quantity_to_send} contrato(s) @${price:.2f}")
                result = self.place_order(self.entry_side, price, quantity_to_send, order_role='ENTRY')
                if result:
                    logger.info(f"[OPEN] [OK] Orden enviada exitosamente")
                    self.allow_entry_topup = True
                    self.last_order_time = now  # Solo actualizar si la orden fue enviada exitosamente
                else:
                    logger.error(f"[OPEN] [ERROR] Error al enviar orden")
                    # No actualizar last_order_time si falló para permitir reintento más rápido
            finally:
                # DESACTIVAR LOCK después de enviar (con delay para prevenir race conditions)
                time.sleep(0.1)  # Pequeño delay para asegurar que la orden se registre
                self._order_lock = False
                logger.info(f"[DEBUG] [LOCK] Lock de orden DESACTIVADO - nuevas órdenes permitidas")
            
        except Exception as e:
            logger.error(f"[ERROR] Error abriendo posición: {e}")
            import traceback
            logger.error(traceback.format_exc())
            # Asegurar que el lock se desactive incluso en caso de error
            self._order_lock = False
            logger.warning(f"[ERROR] [LOCK] Lock forzado a False debido a excepción")
    
    def _execute_partial_exit(self, exit_price: float, quantity: int) -> bool:
        """Ejecuta una salida parcial inmediata a un precio fijo."""
        if not self.position_opened or quantity <= 0 or self.active_order or len(self.active_orders) > 0 or self._order_lock:
            logger.warning(f"[PARTIAL_EXIT] [ERROR] Condiciones no válidas para salida parcial")
            return False
        
        close_side = 'SELL' if self.entry_side_actual == 'BUY' else 'BUY'
        logger.info(f"[PARTIAL_EXIT] Enviando: {close_side} {quantity} @ ${exit_price:.2f}")
        
        self._order_lock = True
        try:
            self.allow_entry_topup = False
            return bool(self.place_order(close_side, exit_price, quantity, order_role='PARTIAL_EXIT'))
        finally:
            time.sleep(0.1)
            self._order_lock = False
    
    def close_position(self, reason: str = "", quantity: Optional[int] = None):
        """
        Cierra posición (completa o parcial)
        
        Args:
            reason: Razón del cierre
            quantity: Cantidad a cerrar (None = cerrar toda la posición)
        """
        logger.info(f"[FUNC_CALL] [CLOSE] close_position() LLAMADO - razón: {reason}, cantidad: {quantity}")
        logger.info("="*70)
        try:
            logger.info(f"[CLOSE] close_position() LLAMADO - Verificando condiciones...")
            logger.info(f"   - Razón: {reason}")
            logger.info(f"   - position_opened: {self.position_opened}")
            logger.info(f"   - entry_side_actual: {self.entry_side_actual}")
            logger.info(f"   - entry_price: ${self.entry_price:.2f}" if self.entry_price else "   - entry_price: None")
            
            if not self.position_opened:
                logger.warning("[CLOSE] [ERROR] No hay posición abierta - ignorando cierre")
                return
            
            # Validar entry_side_actual
            if not self.entry_side_actual:
                logger.error("[CLOSE] [ERROR] No se puede cerrar posición: entry_side_actual no está definido")
                logger.error("[CLOSE] Acción: Forzando cierre del estado inconsistente")
                # Intentar forzar cierre del estado inconsistente
                self.position_opened = False
                return
            
            # Verificar si ya hay una orden de cierre activa
            logger.info(f"[CLOSE] Verificando órdenes activas antes de cerrar...")
            logger.info(f"   - active_order: {self.active_order}")
            logger.info(f"   - active_orders count: {len(self.active_orders)}")
            logger.info(f"   - order_cancel_pending count: {len(self.order_cancel_pending)}")
            logger.info(f"   - _order_lock: {self._order_lock}")
            
            # CRÍTICO: Verificar lock de envío
            if self._order_lock:
                logger.warning(f"[CLOSE] [ERROR] BLOQUEADO: Orden lock activo - otra orden está siendo procesada")
                return
            
            self.allow_entry_topup = False
            
            # CRÍTICO: Verificar si hay órdenes pendientes de cancelación
            if len(self.order_cancel_pending) > 0:
                logger.warning(f"[CLOSE] [WARNING] Hay {len(self.order_cancel_pending)} orden(es) pendiente(s) de cancelación")
                logger.warning(f"[CLOSE] Órdenes pendientes: {list(self.order_cancel_pending)}")
                
                # Verificar si alguna orden pendiente de cancelación ya fue cancelada
                for cl_ord_id in list(self.order_cancel_pending):
                    state = self.order_states.get(cl_ord_id, 'UNKNOWN')
                    if state in ['CANCELLED', 'REJECTED', 'FILLED']:
                        # Ya fue cancelada/ejecutada/rechazada, limpiar flag
                        logger.info(f"[CLOSE] Orden {cl_ord_id} ya está en estado {state}, limpiando flag de cancelación pendiente")
                        self.order_cancel_pending.discard(cl_ord_id)
                
                # Si aún hay órdenes pendientes, no permitir nueva orden de cierre
                if len(self.order_cancel_pending) > 0:
                    logger.warning(f"[CLOSE] [ERROR] BLOQUEADO: Aún hay {len(self.order_cancel_pending)} orden(es) pendiente(s) de confirmación de cancelación")
                    logger.warning(f"[CLOSE] ESPERANDO confirmación de cancelación antes de enviar orden de cierre")
                    return
            
            if self.active_order or len(self.active_orders) > 0:
                logger.warning(f"[CLOSE] [WARNING] Hay orden(es) activa(s) al intentar cerrar")
                # Revisar si alguna es de cierre
                expected_close_side = 'SELL' if self.entry_side_actual == 'BUY' else 'BUY'
                logger.info(f"[CLOSE] Verificando si alguna orden activa es de cierre (expected: {expected_close_side})...")
                
                for cl_ord_id, order_info in self.active_orders.items():
                    logger.info(f"[CLOSE] Revisando orden {cl_ord_id}: side={order_info.get('side')}")
                    if order_info.get('side') == expected_close_side:
                        logger.info(f"[CLOSE] [OK] Ya existe orden de cierre activa: {cl_ord_id}")
                        logger.info(f"[CLOSE] Acción: No enviando nueva orden de cierre")
                        return
                
                logger.warning(f"[CLOSE] [WARNING] Hay órdenes activas pero ninguna es de cierre - esperando...")
                return
            
            # Guardar razón
            self.last_exit_reason = reason or "MANUAL"
            logger.info(f"[CLOSE] Razón de cierre guardada: {self.last_exit_reason}")
            
            # Determinar cantidad a cerrar
            # Si hay tracking de cantidad (salidas parciales previas), usar esa; si no, usar order_quantity
            position_qty = getattr(self, 'position_quantity', None)
            cantidad_disponible = position_qty if position_qty and position_qty > 0 else self.order_quantity
            close_quantity = quantity if quantity is not None and quantity > 0 else cantidad_disponible
            
            # VALIDACIÓN: Para cierres completos, verificar que la posición esté completa
            # ============================================================================
            is_full_close = (quantity is None or quantity <= 0)
            if is_full_close:
                pending_entry_qty = self._get_pending_entry_quantity()
                target_entry_qty = int(round(self.entry_target_quantity if hasattr(self, 'entry_target_quantity') else self.order_quantity))
                total_expected_qty = int(round(position_qty or 0)) + pending_entry_qty
                
                logger.info(f"[CLOSE] Verificando completitud de posición para cierre completo...")
                logger.info(f"[CLOSE]   - Posición ejecutada: {position_qty or 0} contratos")
                logger.info(f"[CLOSE]   - Pendiente de ejecutar: {pending_entry_qty} contratos")
                logger.info(f"[CLOSE]   - Total esperado: {total_expected_qty} contratos")
                logger.info(f"[CLOSE]   - Objetivo: {target_entry_qty} contratos")
                
                if total_expected_qty < target_entry_qty:
                    remaining_qty = target_entry_qty - total_expected_qty
                    logger.warning(f"[CLOSE] [BLOQUEADO] Posición incompleta: faltan {remaining_qty} contrato(s) para alcanzar objetivo de {target_entry_qty}")
                    logger.warning(f"[CLOSE] [BLOQUEADO] No se puede cerrar posición completa hasta que se ejecuten todos los contratos")
                    logger.warning(f"[CLOSE] [BLOQUEADO] Use salida parcial si desea cerrar solo los contratos ejecutados")
                    return
                
                logger.info(f"[CLOSE] [OK] Posición completa: {position_qty or 0} ejecutados + {pending_entry_qty} pendientes = {total_expected_qty} >= {target_entry_qty}")
            
            if quantity is not None and quantity > 0:
                logger.info(f"[CLOSE] Salida PARCIAL: cerrando {close_quantity} de {cantidad_disponible} contrato(s)")
            else:
                logger.info(f"[CLOSE] Cierre COMPLETO: cerrando {close_quantity} contrato(s)")
            
            close_side = 'SELL' if self.entry_side_actual == 'BUY' else 'BUY'
            logger.info(f"[CLOSE] Calculando precio de cierre para {close_side}...")
            logger.info(f"   - Posición actual: {self.entry_side_actual} @ ${self.entry_price:.2f}")
            logger.info(f"   - Side de cierre: {close_side}")
            logger.info(f"   - Cantidad a cerrar: {close_quantity}")
            
            # Si es precio fijo, extraer el precio del reason y usarlo directamente
            fixed_price = None
            if reason and reason.startswith("FIXED_PRICE_") and "_FULL" in reason:
                try:
                    # Extraer precio de formato: FIXED_PRICE_1512.00_FULL
                    price_str = reason.replace("FIXED_PRICE_", "").replace("_FULL", "")
                    fixed_price = float(price_str)
                    logger.info(f"[CLOSE] [FIXED_PRICE] Usando precio fijo extraído: ${fixed_price:.2f}")
                except (ValueError, AttributeError) as e:
                    logger.warning(f"[CLOSE] [WARNING] No se pudo extraer precio fijo de reason '{reason}': {e}")
                    fixed_price = None
            
            # CRÍTICO: Calcular precio objetivo del TP para validar que el precio de cierre sea válido
            # REGLA: 
            # - Para BUY (long): TP = entry_price + (target_profit_ticks * tick_size) → precio objetivo MAYOR que entrada
            # - Para SELL (short): TP = entry_price - (target_profit_ticks * tick_size) → precio objetivo MENOR que entrada
            target_exit_price = None
            if self.target_profit_ticks and self.target_profit_ticks > 0:
                if self.entry_side_actual == 'BUY':
                    # Para BUY: TP = entry_price + target_profit_ticks * tick_size
                    # Ejemplo: entrada $1535.0, TP 1 tick (0.5) → objetivo $1535.5
                    target_exit_price = self.entry_price + (self.target_profit_ticks * self.tick_size)
                    logger.info(f"[CLOSE] BUY: Precio objetivo TP = ${self.entry_price:.2f} + ({self.target_profit_ticks} * ${self.tick_size:.2f}) = ${target_exit_price:.2f}")
                else:  # SELL
                    # Para SELL: TP = entry_price - target_profit_ticks * tick_size
                    # Ejemplo: entrada $1535.0, TP 1 tick (0.5) → objetivo $1534.5 (NO $1535.5)
                    target_exit_price = self.entry_price - (self.target_profit_ticks * self.tick_size)
                    logger.info(f"[CLOSE] SELL: Precio objetivo TP = ${self.entry_price:.2f} - ({self.target_profit_ticks} * ${self.tick_size:.2f}) = ${target_exit_price:.2f}")
                
                logger.info(f"[CLOSE] Precio objetivo TP: ${target_exit_price:.2f} | Entry: ${self.entry_price:.2f} | TP: {self.target_profit_ticks} ticks")
            
            # Si hay precio fijo, usarlo directamente; si no, calcular precio según razón de cierre
            if fixed_price is not None:
                price = fixed_price
                logger.info(f"[CLOSE] [FIXED_PRICE] Usando precio fijo directamente: ${price:.2f}")
                # Para precios fijos, no validar TP objetivo (es un precio específico configurado por el usuario)
            else:
                # CRÍTICO: Para salidas críticas (TP/SL/TIME), usar EJECUCIÓN INMEDIATA
                # Solo usar PRICE_IMPROVEMENT para salidas manuales o estratégicas
                critical_exits = [
                    "TAKE_PROFIT", "STOP_LOSS", "TIME_EXIT", "BREAK_EVEN",
                    "STOP_LOSS_TIME_BASED", "STOP_LOSS_IMMEDIATE"
                ]
                # También incluir variantes de TAKE_PROFIT con sufijos
                is_critical = reason in critical_exits or (reason and reason.startswith("TAKE_PROFIT_"))
                
                if is_critical:
                    # EJECUCIÓN INMEDIATA: cruzar el mercado para asegurar la salida
                    logger.info(f"[CLOSE] Salida crítica ({reason}): usando EJECUCIÓN INMEDIATA")
                    if close_side == 'SELL':
                        # Para cerrar BUY: vender al BID (donde están los compradores)
                        price = self.market_data.get('bid')
                        logger.info(f"[CLOSE] [IMMEDIATE] SELL al BID: ${price:.2f}" if price else "[CLOSE] [ERROR] BID no disponible")
                    else:  # BUY
                        # Para cerrar SELL: comprar al OFFER (donde están los vendedores)
                        price = self.market_data.get('offer')
                        logger.info(f"[CLOSE] [IMMEDIATE] BUY al OFFER: ${price:.2f}" if price else "[CLOSE] [ERROR] OFFER no disponible")
                    
                    if price is None:
                        logger.error(f"[CLOSE] [ERROR] No se puede ejecutar salida inmediata: precio no disponible")
                        logger.error(f"[CLOSE] BID: {self.market_data.get('bid')}, OFFER: {self.market_data.get('offer')}")
                        return
                else:
                    # Salidas no críticas: usar mejora de precio para optimizar
                    logger.info(f"[CLOSE] Salida no crítica: intentando precio mejorado para quedar primero en book...")
                    improved = self.get_improved_price(close_side)
                    if improved is not None:
                        price = improved
                        logger.info(f"[CLOSE] [OK] Precio mejorado obtenido: ${price:.2f}")
                    
                    # CRÍTICO: Validar que el precio de cierre respeta el TP (no cierra con pérdida cuando TP fue alcanzado)
                    if target_exit_price is not None:
                        if self.entry_side_actual == 'BUY':
                            # Para BUY: cerrar con SELL, precio de cierre (BID) debe ser >= precio objetivo TP
                            # Si el precio mejorado es menor que el TP objetivo, ajustar
                            if price < target_exit_price:
                                logger.warning(f"[CLOSE] [WARNING] Precio mejorado ${price:.2f} < TP objetivo ${target_exit_price:.2f}")
                                logger.warning(f"[CLOSE] Ajustando precio para asegurar que respete TP objetivo")
                                # Para cerrar BUY, necesitamos BID (donde vendemos), y debe ser >= TP objetivo
                                bid = self.market_data.get('bid')
                                if bid and bid >= target_exit_price:
                                    # Usar el máximo entre el precio mejorado y el TP objetivo, pero limitado al BID disponible
                                    price = min(bid, max(target_exit_price, improved))
                                    logger.info(f"[CLOSE] Precio ajustado para respetar TP: ${price:.2f} (TP objetivo: ${target_exit_price:.2f}, BID disponible: ${bid:.2f})")
                                else:
                                    logger.warning(f"[CLOSE] BID actual ${bid:.2f} < TP objetivo ${target_exit_price:.2f}")
                                    logger.warning(f"[CLOSE] El mercado no permite cerrar en TP objetivo - usando mejor precio disponible")
                        else:  # SELL
                            # Para SELL: cerrar con BUY, precio de cierre (OFFER) debe ser <= precio objetivo TP
                            # Si el precio mejorado es mayor que el TP objetivo, ajustar
                            if price > target_exit_price:
                                logger.warning(f"[CLOSE] [WARNING] Precio mejorado ${price:.2f} > TP objetivo ${target_exit_price:.2f}")
                                logger.warning(f"[CLOSE] Ajustando precio para asegurar que respete TP objetivo")
                                # Para cerrar SELL, necesitamos OFFER (donde compramos), y debe ser <= TP objetivo
                                offer = self.market_data.get('offer')
                                if offer and offer <= target_exit_price:
                                    # Usar el mínimo entre el precio mejorado y el TP objetivo, pero limitado al OFFER disponible
                                    price = max(offer, min(target_exit_price, improved))
                                    logger.info(f"[CLOSE] Precio ajustado para respetar TP: ${price:.2f} (TP objetivo: ${target_exit_price:.2f}, OFFER disponible: ${offer:.2f})")
                                else:
                                    logger.warning(f"[CLOSE] OFFER actual ${offer:.2f} > TP objetivo ${target_exit_price:.2f}")
                                    logger.warning(f"[CLOSE] El mercado no permite cerrar en TP objetivo - usando mejor precio disponible")
                    else:
                        logger.warning(f"[CLOSE] [WARNING] No se pudo obtener precio mejorado, usando precio directo del mercado...")
                        # Fallback a precio directo del mercado, validando None
                        if close_side == 'BUY':
                            price = self.market_data.get('offer')
                            logger.info(f"[CLOSE] Usando OFFER como precio directo: ${price:.2f}" if price else "[CLOSE] OFFER es None")
                        else:
                            price = self.market_data.get('bid')
                            logger.info(f"[CLOSE] Usando BID como precio directo: ${price:.2f}" if price else "[CLOSE] BID es None")
                        
                        # Si aún es None, no podemos cerrar
                        if price is None:
                            logger.error(f"[CLOSE] [ERROR] No se puede cerrar: No hay precio disponible")
                            logger.error(f"[CLOSE] BID: {self.market_data.get('bid')}, OFFER: {self.market_data.get('offer')}")
                            logger.error(f"[ERROR] No se puede cerrar posición: precio {close_side} no disponible")
                            return
                    
                    # CRÍTICO: Validar precio directo contra TP objetivo
                if target_exit_price is not None:
                    if self.entry_side_actual == 'BUY':
                        # Para BUY: cerrar con SELL, precio debe ser >= TP objetivo (vendemos al BID)
                        if price < target_exit_price:
                            logger.warning(f"[CLOSE] [WARNING] Precio directo ${price:.2f} < TP objetivo ${target_exit_price:.2f}")
                            logger.warning(f"[CLOSE] El mercado no permite cerrar en TP objetivo - verificando si hay mejor precio...")
                            # Intentar usar BID si es mejor que OFFER para cerrar BUY
                            bid = self.market_data.get('bid')
                            if bid and bid >= target_exit_price:
                                price = bid
                                logger.info(f"[CLOSE] Usando BID ${price:.2f} que permite cerrar en TP objetivo")
                            else:
                                logger.warning(f"[CLOSE] BID ${bid:.2f} tampoco permite TP objetivo ${target_exit_price:.2f} - usando mejor precio disponible")
                    else:  # SELL
                        # Para SELL: cerrar con BUY, precio debe ser <= TP objetivo (compramos al OFFER)
                        if price > target_exit_price:
                            logger.warning(f"[CLOSE] [WARNING] Precio directo ${price:.2f} > TP objetivo ${target_exit_price:.2f}")
                            logger.warning(f"[CLOSE] El mercado no permite cerrar en TP objetivo - verificando si hay mejor precio...")
                            # Intentar usar OFFER si es mejor que BID para cerrar SELL
                            offer = self.market_data.get('offer')
                            if offer and offer <= target_exit_price:
                                price = offer
                                logger.info(f"[CLOSE] Usando OFFER ${price:.2f} que permite cerrar en TP objetivo")
                            else:
                                logger.warning(f"[CLOSE] OFFER ${offer:.2f} tampoco permite TP objetivo ${target_exit_price:.2f} - usando mejor precio disponible")
            
            # CRÍTICO: Validación final del precio de cierre
            # IMPORTANTE: Si es STOP_LOSS, permitir cerrar con pérdida (es la naturaleza del stop loss)
            allow_loss = (reason == "STOP_LOSS" or reason.startswith("STOP_LOSS"))
            
            if price is not None:
                if self.entry_side_actual == 'SELL':
                    # Para SELL: precio de cierre (compra) debe ser <= entry_price para tener ganancia
                    if price > self.entry_price and not allow_loss:
                        logger.error(f"[CLOSE] [ERROR] Precio de cierre ${price:.2f} > entry_price ${self.entry_price:.2f} - esto resultaría en PÉRDIDA")
                        logger.error(f"[CLOSE] No se puede cerrar con pérdida sistemática - verificando mercado...")
                        # Usar BID directo si es mejor
                        bid = self.market_data.get('bid')
                        if bid and bid < self.entry_price:
                            price = bid
                            logger.info(f"[CLOSE] Usando BID directo ${price:.2f} que permite ganancia")
                        else:
                            logger.error(f"[CLOSE] [ERROR] No se puede cerrar con ganancia - BID=${bid:.2f}, entry=${self.entry_price:.2f}")
                            return
                    elif price > self.entry_price and allow_loss:
                        logger.warning(f"[CLOSE] [STOP_LOSS] Cerrando con pérdida: ${price:.2f} > ${self.entry_price:.2f} (STOP_LOSS activado)")
                else:  # BUY
                    # Para BUY: precio de cierre (venta) debe ser >= entry_price para tener ganancia
                    if price < self.entry_price and not allow_loss:
                        logger.error(f"[CLOSE] [ERROR] Precio de cierre ${price:.2f} < entry_price ${self.entry_price:.2f} - esto resultaría en PÉRDIDA")
                        logger.error(f"[CLOSE] No se puede cerrar con pérdida sistemática - verificando mercado...")
                        # Usar OFFER directo si es mejor
                        offer = self.market_data.get('offer')
                        if offer and offer > self.entry_price:
                            price = offer
                            logger.info(f"[CLOSE] Usando OFFER directo ${price:.2f} que permite ganancia")
                        else:
                            logger.error(f"[CLOSE] [ERROR] No se puede cerrar con ganancia - OFFER=${offer:.2f}, entry=${self.entry_price:.2f}")
                            return
                    elif price < self.entry_price and allow_loss:
                        logger.warning(f"[CLOSE] [STOP_LOSS] Cerrando con pérdida: ${price:.2f} < ${self.entry_price:.2f} (STOP_LOSS activado)")
            
            # VERIFICACIÓN FINAL antes de enviar orden de cierre
            logger.info(f"[CLOSE] VERIFICACIÓN FINAL antes de enviar orden de cierre:")
            logger.info(f"   - active_order: {self.active_order}")
            logger.info(f"   - active_orders count: {len(self.active_orders)}")
            logger.info(f"   - order_cancel_pending count: {len(self.order_cancel_pending)}")
            logger.info(f"   - _order_lock: {self._order_lock}")
            
            # Doble verificación
            if self.active_order or len(self.active_orders) > 0:
                logger.error(f"[CLOSE] [ERROR] DOBLE CHECK FALLIDO: Hay órdenes activas justo antes de enviar cierre - ABORTANDO")
                return
            
            if len(self.order_cancel_pending) > 0:
                logger.error(f"[CLOSE] [ERROR] DOBLE CHECK FALLIDO: Hay cancelaciones pendientes justo antes de enviar cierre - ABORTANDO")
                return
            
            if self._order_lock:
                logger.error(f"[CLOSE] [ERROR] DOBLE CHECK FALLIDO: Lock activo justo antes de enviar cierre - ABORTANDO")
                return
            
            # ACTIVAR LOCK antes de enviar
            self._order_lock = True
            self._last_order_send_attempt = time.time()
            logger.info(f"[CLOSE] [LOCK] Lock de orden ACTIVADO - previene múltiples envíos")
            
            try:
                logger.info(f"[CLOSE] Enviando orden de cierre: {close_side} @${price:.2f}")
                logger.info(f"[CLOSE] Cantidad: {self.order_quantity}")
                logger.info(f"[CLOSE] Razón: {self.last_exit_reason}")
                
                result = self.place_order(close_side, price, close_quantity, order_role='EXIT')
                if result:
                    logger.info(f"[CLOSE] [OK] Orden de cierre enviada exitosamente ({close_quantity} contrato(s))")
                    logger.info(f"[CLOSE] Esperando ejecución para cerrar posición...")
                else:
                    logger.error(f"[CLOSE] [ERROR] Error al enviar orden de cierre")
                    logger.error(f"[CLOSE] La posición permanece abierta - se intentará cerrar nuevamente")
            finally:
                # DESACTIVAR LOCK después de enviar
                time.sleep(0.1)  # Pequeño delay para asegurar que la orden se registre
                self._order_lock = False
                logger.info(f"[CLOSE] [LOCK] Lock de orden DESACTIVADO - nuevas órdenes permitidas")
            
        except Exception as e:
            logger.error(f"[ERROR] Error cerrando posición: {e}")
            import traceback
            logger.error(f"[ERROR] Traceback:\n{traceback.format_exc()}")
            # Asegurar que el lock se desactive incluso en caso de error
            self._order_lock = False
            logger.warning(f"[ERROR] [LOCK] Lock forzado a False debido a excepción")
    
    def check_websocket_health(self):
        """Verifica que el WebSocket esté recibiendo datos (health check)"""
        # Logging throttled - solo cada 30 segundos
        if not hasattr(self, '_last_health_check_log'):
            self._last_health_check_log = 0
        
        now = time.time()
        should_log = (now - self._last_health_check_log) >= 30
        
        if should_log:
            logger.debug(f"[FUNC_CALL] [WS_HEALTH] check_websocket_health() LLAMADO")
            self._last_health_check_log = now
        
        if not self.websocket_connected:
            return
        
        if self.last_market_data_time is None:
            # Aún no recibimos data, está bien si acaba de iniciar
            if time.time() - (self.calibration_start_time or time.time()) < 10:
                return
            else:
                logger.warning("[WARNING] WebSocket iniciado pero sin market data recibido")
                self._reconnect_websocket()
            return
        
        time_since_last = time.time() - self.last_market_data_time
        if time_since_last > self.websocket_timeout_seconds:
            logger.warning(f"[WARNING] Sin market data por {time_since_last:.0f}s (timeout: {self.websocket_timeout_seconds}s)")
            logger.warning("[WARNING] WebSocket puede estar desconectado - intentando reconectar...")
            self.websocket_connected = False
            self._reconnect_websocket()
    
    def _reconnect_websocket(self, delay: float = 5.0):
        """Reconectar WebSocket automáticamente con backoff exponencial"""
        logger.info(f"[FUNC_CALL] [WS_RECONNECT] _reconnect_websocket() LLAMADO - delay: {delay}s, intento: {self.websocket_reconnect_attempts+1}/{self.max_reconnect_attempts}")
        if self.websocket_reconnect_attempts >= self.max_reconnect_attempts:
            logger.error(f"[ERROR] Máximo de intentos de reconexión alcanzado ({self.max_reconnect_attempts})")
            logger.error("[ERROR] Bot continuará pero sin WebSocket - algunas funcionalidades pueden estar limitadas")
            return False
        
        self.websocket_reconnect_attempts += 1
        
        try:
            logger.info(f"[RECONNECT] Intentando reconectar WebSocket (intento {self.websocket_reconnect_attempts}/{self.max_reconnect_attempts})...")
            
            # Cerrar conexión anterior si existe
            try:
                pyRofex.close_websocket_connection()
                logger.info("[RECONNECT] Conexión anterior cerrada")
                time.sleep(1)
            except Exception as close_error:
                logger.warning(f"[WARNING] Error cerrando conexión anterior (puede ser normal): {close_error}")
            
            # Iniciar nueva conexión
            logger.info("[RECONNECT] Iniciando nueva conexión WebSocket...")
            pyRofex.init_websocket_connection(
                market_data_handler=self._market_data_handler,
                order_report_handler=self._order_report_handler,
                error_handler=self._error_handler,
                exception_handler=self._exception_handler
            )
            
            time.sleep(2)  # Esperar a que se establezca la conexión
            
            # Re-suscribir a market data
            pyRofex.market_data_subscription(
                tickers=[self.future_symbol],
                entries=[
                    pyRofex.MarketDataEntry.BIDS,
                    pyRofex.MarketDataEntry.OFFERS,
                    pyRofex.MarketDataEntry.LAST
                ]
            )
            
            time.sleep(1)
            
            # Re-suscribir a reportes de órdenes
            pyRofex.order_report_subscription()
            
            # Resetear estado
            self.websocket_connected = True
            reconnect_time = time.time()
            self.last_market_data_time = reconnect_time
            self.websocket_reconnect_attempts = 0
            
            # CRÍTICO: Actualizar timestamp del market_data para evitar bloqueos por "datos obsoletos"
            # después de reconexión (el timestamp anterior podría ser muy viejo)
            if self.market_data.get('timestamp'):
                # Solo actualizar si el timestamp es muy antiguo (>10s), de lo contrario mantener el último recibido
                old_timestamp = self.market_data.get('timestamp')
                if reconnect_time - old_timestamp > 10:
                    logger.info(f"[RECONNECT] Actualizando timestamp de market_data tras reconexión (anterior: {reconnect_time - old_timestamp:.1f}s)")
                    self.market_data['timestamp'] = reconnect_time
                else:
                    logger.debug(f"[RECONNECT] Manteniendo timestamp reciente de market_data ({reconnect_time - old_timestamp:.1f}s)")
            else:
                # Si no hay timestamp, establecer uno reciente para evitar bloqueos
                self.market_data['timestamp'] = reconnect_time
                logger.info(f"[RECONNECT] Estableciendo timestamp inicial de market_data tras reconexión")
            
            logger.info("[OK] WebSocket reconectado exitosamente")
            return True
            
        except Exception as e:
            logger.error(f"[ERROR] Error en intento de reconexión {self.websocket_reconnect_attempts}: {e}")
            
            # Reintentar con backoff exponencial
            if self.websocket_reconnect_attempts < self.max_reconnect_attempts:
                next_delay = delay * (self.websocket_reconnect_attempts + 1)
                logger.info(f"[RECONNECT] Reintentando en {next_delay:.1f}s...")
                time.sleep(next_delay)
                return self._reconnect_websocket(delay=next_delay)
            else:
                logger.error(f"[ERROR] No se pudo reconectar WebSocket después de {self.max_reconnect_attempts} intentos")
                return False
    
    def check_operations_limit(self) -> Tuple[bool, str]:
        """Verifica si se alcanzó el límite de operaciones"""
        logger.debug(f"[FUNC_CALL] check_operations_limit() LLAMADO")
        # Resetear contador diario si cambió el día
        today = datetime.now().date()
        if today > self.last_operations_reset_date:
            logger.info(f"[INFO] Nuevo día - reseteando contador diario de operaciones")
            self.operations_count_today = 0
            self.last_operations_reset_date = today
        
        # Verificar límite diario
        if self.max_operations_per_day is not None:
            if self.operations_count_today >= self.max_operations_per_day:
                return False, f"Límite diario alcanzado: {self.operations_count_today}/{self.max_operations_per_day}"
        
        # Verificar límite total
        if self.max_operations_total is not None:
            if self.operations_count_total >= self.max_operations_total:
                return False, f"Límite total alcanzado: {self.operations_count_total}/{self.max_operations_total}"
        
        return True, f"OK ({self.operations_count_today}/{self.max_operations_per_day if self.max_operations_per_day else '∞'} hoy, {self.operations_count_total}/{self.max_operations_total if self.max_operations_total else '∞'} total)"
    
    def register_operation(self, operation_type: str = "TRADE"):
        """Registra una operación completada"""
        logger.info(f"[FUNC_CALL] [REGISTER] register_operation() LLAMADO - tipo: {operation_type}")
        self.operations_count_today += 1
        self.operations_count_total += 1
        self.operations_history.append({
            'timestamp': time.time(),
            'type': operation_type,
            'count_today': self.operations_count_today,
            'count_total': self.operations_count_total
        })
        # Mantener solo últimas 100 operaciones en historial
        if len(self.operations_history) > 100:
            self.operations_history.pop(0)
    
    def check_trading_opportunity(self):
        """Verifica oportunidades de trading"""
        try:
            if not self.running:
                return
            
            can_operate, _ = self.check_operations_limit()
            if not can_operate:
                return
            
            self.check_websocket_health()
            
            if not self.is_calibration_complete:
                return
            
            self.check_order_timeout()
            
            # Verificar órdenes activas (común para abrir y cerrar)
            can_operate_order = (not self.active_order and 
                                len(self.active_orders) == 0 and 
                                len(self.order_cancel_pending) == 0 and
                                not self._order_lock)
            
            position_qty = int(round(self.position_quantity)) if hasattr(self, 'position_quantity') else 0
            pending_entry_qty = self._get_pending_entry_quantity()
            target_entry_qty = int(round(self.entry_target_quantity if hasattr(self, 'entry_target_quantity') else self.order_quantity))
            remaining_entry_qty = max(0, int(round(target_entry_qty - (position_qty + pending_entry_qty))))
            self.position_opened = position_qty > 0
            
            if position_qty > 0:
                if not self.entry_side_actual:
                    self.entry_side_actual = self.entry_side
                if not self.entry_price:
                    logger.debug("[CHECK_OPPORTUNITY] entry_price no definido, no se evalúa salida todavía")
                else:
                    should_exit, reason = self.check_exit_conditions()
                    if should_exit and can_operate_order:
                        self.close_position(reason)
                        return
                if remaining_entry_qty > 0:
                    if self.allow_entry_topup and can_operate_order:
                        logger.info(f"[CHECK_OPPORTUNITY] Faltan {remaining_entry_qty} contrato(s) para alcanzar objetivo {target_entry_qty}; enviando orden de refuerzo")
                        self.open_position(quantity_override=remaining_entry_qty, allow_existing_position=True)
                    else:
                        logger.debug(f"[CHECK_OPPORTUNITY] Posición abierta con {position_qty} contrato(s); top-up deshabilitado o condiciones no válidas (restante: {remaining_entry_qty})")
            else:
                if can_operate_order and remaining_entry_qty > 0:
                    self.open_position(quantity_override=remaining_entry_qty)
        
        except Exception as e:
            logger.error(f"[ERROR] Error en check_trading_opportunity: {e}")
            import traceback
            logger.error(traceback.format_exc())
    
    # =============================================================================
    # EJECUCIÓN
    # =============================================================================
    
    def run(self, duration: Optional[int] = None):
        """Ejecutar el bot"""
        logger.info("="*70)
        logger.info("[FUNC_CALL] run() LLAMADO")
        logger.info("="*70)
        self.running = True
        start_time = time.time()
        
        logger.info("[START] BOT INICIADO")
        logger.info(f"   - Duración: {duration}s" if duration else "   - Duración: Ilimitada")
        
        try:
            while self.running:
                if duration and (time.time() - start_time) >= duration:
                    logger.info("[INFO] Duracion completada")
                    break
                
                # Verificar salud del WebSocket periódicamente
                self.check_websocket_health()
                
                # Verificar oportunidades de trading (esto es lo que ejecuta las órdenes)
                self.check_trading_opportunity()
                
                # Mostrar estado periódicamente
                self.show_status()
                time.sleep(5)  # Reducido a 5 segundos para más responsividad
                
        except KeyboardInterrupt:
            logger.info("[INFO] Interrupcion por usuario")
        finally:
            self.stop()
    
    def show_status(self):
        """Muestra estado del bot"""
        # Logging throttled - solo cada 30 segundos para no saturar
        if not hasattr(self, '_last_status_log'):
            self._last_status_log = 0
        
        now = time.time()
        should_log = (now - self._last_status_log) >= 30
        
        if should_log:
            logger.debug(f"[FUNC_CALL] [STATUS] show_status() LLAMADO")
            self._last_status_log = now
        
        logger.info("="*70)
        logger.info(f"[INFO] ESTADO - {datetime.now().strftime('%H:%M:%S')}")
        
        # Mostrar puntas del libro de órdenes
        bid = self.market_data.get('bid')
        offer = self.market_data.get('offer')
        last = self.market_data.get('last')
        
        if bid and offer:
            spread = offer - bid
            logger.info(f"[BOOK] {self.future_symbol} | BID: ${bid:.2f} | OFFER: ${offer:.2f} | Spread: ${spread:.2f}")
            bid_size = self.market_data.get('bid_size')
            offer_size = self.market_data.get('offer_size')
            bid_depth = self.market_data.get('bid_depth')
            offer_depth = self.market_data.get('offer_depth')
            if isinstance(bid_size, (int, float)) or isinstance(offer_size, (int, float)):
                logger.info(f"[DEPTH] Top size → BID: {bid_size if bid_size else 0:.0f} | OFFER: {offer_size if offer_size else 0:.0f}")
            if isinstance(bid_depth, (int, float)) or isinstance(offer_depth, (int, float)):
                logger.info(f"[DEPTH] {self.depth_levels_to_track} niveles → BID: {bid_depth if bid_depth else 0:.0f} | OFFER: {offer_depth if offer_depth else 0:.0f}")
        elif last:
            logger.info(f"[PRICE] {self.future_symbol}: ${last:.2f}")
        
        # Mostrar precio de ejecución que se usará
        if not self.position_opened:
            if self.entry_side == 'BUY':
                exec_price = offer if offer else last
                if exec_price and hasattr(self, 'entry_max_price') and self.entry_max_price is not None:
                    if exec_price <= self.entry_max_price:
                        logger.info(f"[INFO] Condicion CUMPLIDA: OFFER ${exec_price:.2f} <= ${self.entry_max_price:.2f} (COMPRARÁ)")
                    else:
                        logger.info(f"[INFO] Esperando: OFFER ${exec_price:.2f} > ${self.entry_max_price:.2f} (esperando OFFER <= ${self.entry_max_price:.2f})")
            else:  # SELL
                exec_price = bid if bid else last
                if exec_price and hasattr(self, 'entry_min_price') and self.entry_min_price is not None:
                    if exec_price >= self.entry_min_price:
                        logger.info(f"[INFO] Condicion CUMPLIDA: BID ${exec_price:.2f} >= ${self.entry_min_price:.2f} (VENDERÁ)")
                    else:
                        logger.info(f"[INFO] Esperando: BID ${exec_price:.2f} < ${self.entry_min_price:.2f} (esperando BID >= ${self.entry_min_price:.2f})")
        
        if self.enable_latency_filter:
            if self.is_latency_calibrated and self.latency_baseline_ms is not None and self.latency_baseline_ms > 0:
                logger.info(f"[LATENCY] Filtro: ACTIVO | {self.last_latency*1000:.1f}ms (baseline: {self.latency_baseline_ms:.1f}ms)")
            else:
                if hasattr(self, 'calibration_start_time') and self.calibration_start_time:
                    elapsed = time.time() - self.calibration_start_time
                    remaining = max(0, self.calibration_period_seconds - elapsed)
                    logger.info(f"[LATENCY] Calibrando... {remaining:.0f}s restantes")
        else:
            logger.info(f"[LATENCY] Filtro: DESACTIVADO | Operando sin restricciones")
        
        if self.position_opened:
            logger.info(f"[POSITION] POSICION ABIERTA:")
            logger.info(f"   - Lado: {self.entry_side_actual}")
            logger.info(f"   - Precio entrada: ${self.entry_price}")
            if self.entry_time:
                minutes = (time.time() - self.entry_time) / 60
                logger.info(f"   - Tiempo: {minutes:.0f} minutos")
        else:
            logger.info(f"[POSITION] Sin posicion abierta")
        
        logger.info(f"[ORDERS] Ordenes activas: {len(self.active_orders)}")
        
        # Mostrar contador de operaciones
        limit_info = []
        if self.max_operations_per_day is not None:
            limit_info.append(f"{self.operations_count_today}/{self.max_operations_per_day} hoy")
        if self.max_operations_total is not None:
            limit_info.append(f"{self.operations_count_total}/{self.max_operations_total} total")
        
        if limit_info:
            logger.info(f"[OPERATIONS] Operaciones: {', '.join(limit_info)}")
        else:
            logger.info(f"[OPERATIONS] Operaciones: {self.operations_count_today} hoy, {self.operations_count_total} total (sin límite)")
        
        logger.info("="*70)
    
    def stop(self):
        """Detiene el bot"""
        logger.info("="*70)
        logger.info("[FUNC_CALL] [STOP] stop() LLAMADO")
        logger.info("="*70)
        self.running = False
        logger.info("[STOP] Deteniendo bot...")
        
        # Cancelar todas las órdenes activas
        try:
            logger.info("[CANCEL] Cancelando todas las órdenes activas")
            for cl_ord_id in list(self.active_orders.keys()):
                try:
                    # CRÍTICO: Usar proprietary desde la orden guardada según manual
                    order_info_stop = self.active_orders.get(cl_ord_id, {})
                    proprietary_to_use = order_info_stop.get('proprietary', self.proprietary) if order_info_stop else self.proprietary
                    if not proprietary_to_use:
                        proprietary_to_use = 'api'
                    # Llamar con parámetros directos según manual Primary API
                    pyRofex.cancel_order(client_order_id=cl_ord_id, proprietary=proprietary_to_use)
                    logger.info(f"[OK] Orden {cl_ord_id} cancelada")
                except Exception as e:
                    logger.warning(f"[WARNING] Error cancelando {cl_ord_id}: {e}")
        except Exception as e:
            logger.warning(f"[WARNING] Error en proceso de cancelación: {e}")
        
        # Guardar gráfico final de latencia
        try:
            logger.info("[PLOT] Generando gráfico final de latencia...")
            self._save_latency_plot()
        except Exception as e:
            logger.warning(f"[WARNING] Error generando gráfico de latencia: {e}")
        
        # Cerrar WebSocket
        try:
            if self.websocket_connected:
                pyRofex.close_websocket_connection()
                logger.info("[OK] WebSocket cerrado")
        except Exception as e:
            logger.warning(f"[WARNING] Error cerrando WebSocket: {e}")
        
        logger.info("[OK] BOT DETENIDO")

# =============================================================================
# FUNCIÓN PRINCIPAL
# =============================================================================

def main():
    """Ejecuta el bot de manera interactiva"""
    print("\n" + "="*80)
    print(" "*25 + "PRICE-BASED TRADING BOT")
    print(" "*20 + "Opera por Niveles de Precio Puro")
    print("="*80)
    
    # ============================================================================
    # 1. CONFIGURACIÓN DEL INSTRUMENTO
    # ============================================================================
    print("\n[1] CONFIGURACIÓN DEL INSTRUMENTO")
    print("-" * 80)
    print("   Configure el futuro que desea operar")
    print()
    
    while True:
        future_symbol = input("   Símbolo del futuro (ej: DLR/MAY26) [DLR/MAY26]: ").strip() or "DLR/MAY26"
        if "/" in future_symbol:
            break
        print("   Error: El símbolo debe incluir '/' (ej: DLR/MAY26)")
    
    while True:
        try:
            tick_input = input("   Tick size en dólares (ej: 0.5 para DLR) [0.5]: ").strip() or "0.5"
            tick_size = float(tick_input)
            if tick_size > 0:
                break
            print("   Error: El tick size debe ser mayor a 0")
        except ValueError:
            print("   Error: Ingrese un número válido")
    
    while True:
        try:
            qty_input = input("   Cantidad de contratos [1]: ").strip() or "1"
            order_quantity = int(qty_input)
            if order_quantity > 0:
                break
            print("   Error: La cantidad debe ser mayor a 0")
        except ValueError:
            print("   Error: Ingrese un número entero válido")
    
    # ============================================================================
    # 2. ESTRATEGIA DE ENTRADA
    # ============================================================================
    print("\n[2] ESTRATEGIA DE ENTRADA")
    print("-" * 80)
    print("   Seleccione la dirección de la operación y el nivel de precio")
    print()
    print("   1. COMPRAR (BUY)  → Abrir posición cuando precio <= precio máximo")
    print("   2. VENDER (SELL)  → Abrir posición cuando precio >= precio mínimo")
    print()
    
    while True:
        entry_side_num = input("   Seleccione opción (1 o 2) [1]: ").strip() or "1"
        if entry_side_num in ["1", "2"]:
            break
        print("   Error: Debe seleccionar 1 o 2")
    
    entry_side = "BUY" if entry_side_num == "1" else "SELL"
    
    if entry_side == "BUY":
        print(f"\n   Estrategia: COMPRAR cuando el precio sea menor o igual a cierto nivel")
        while True:
            try:
                price_input = input("   Precio MÁXIMO para comprar (USD) [1665]: ").strip() or "1665"
                entry_max_price = float(price_input)
                if entry_max_price > 0:
                    break
                print("   Error: El precio debe ser mayor a 0")
            except ValueError:
                print("   Error: Ingrese un número válido")
        entry_min_price = None
        print(f"   Comprará cuando BID <= ${entry_max_price:.2f}")
    else:
        print(f"\n   Estrategia: VENDER cuando el precio sea mayor o igual a cierto nivel")
        while True:
            try:
                price_input = input("   Precio MÍNIMO para vender (USD) [1665]: ").strip() or "1665"
                entry_min_price = float(price_input)
                if entry_min_price > 0:
                    break
                print("   Error: El precio debe ser mayor a 0")
            except ValueError:
                print("   Error: Ingrese un número válido")
        entry_max_price = None
        print(f"   Venderá cuando BID >= ${entry_min_price:.2f}")
    
    # ============================================================================
    # 3. ESTRATEGIA DE SALIDA
    # ============================================================================
    print("\n[3] CONDICIONES DE SALIDA")
    print("-" * 80)
    print("   Configure cuándo cerrar la posición automáticamente")
    print()
    print("   Take Profit: Cerrar cuando la ganancia alcance X ticks")
    print("   Stop Loss:   Cerrar cuando la pérdida alcance X ticks")
    print("   Time Exit:   Cerrar después de X minutos (0 = desactivado)")
    print()
    
    while True:
        try:
            tp_input = input("   Take Profit (ticks) [10]: ").strip() or "10"
            target_profit_ticks = float(tp_input)
            if target_profit_ticks >= 0.5:
                break
            print("   Error: El Take Profit debe ser mayor o igual a 0.5 ticks")
        except ValueError:
            print("   Error: Ingrese un número válido (puede ser decimal, ej: 0.5)")
    
    while True:
        try:
            sl_input = input("   Stop Loss (ticks) [5]: ").strip() or "5"
            target_stop_loss_ticks = int(sl_input)
            if target_stop_loss_ticks > 0:
                break
            print("   Error: El Stop Loss debe ser mayor a 0")
        except ValueError:
            print("   Error: Ingrese un número entero válido")
    
    while True:
        try:
            time_input = input("   Time Exit (minutos, 0=desactivado) [120]: ").strip() or "120"
            target_time_exit_minutes = int(time_input)
            if target_time_exit_minutes >= 0:
                if target_time_exit_minutes == 0:
                    target_time_exit_minutes = None
                    print("   Time Exit desactivado")
                break
            print("   Error: El Time Exit debe ser >= 0")
        except ValueError:
            print("   Error: Ingrese un número entero válido")
    
    # ============================================================================
    # GESTIÓN DE POSICIÓN BASADA EN TIEMPO (TP DEGRADADO)
    # ============================================================================
    print("\n[4] GESTIÓN DE POSICIÓN BASADA EN TIEMPO")
    print("-" * 80)
    print("   Activar degradación progresiva del Take Profit:")
    print("   - 0-1 min: TP inicial (ej: 1 tick)")
    print("   - 1-2 min: TP degradado (ej: 0.5 ticks)")
    print("   - 2-3 min: Break even (cerrar en 0)")
    print("   - 3+ min: Aplicar Stop Loss")
    print()
    
    while True:
        enable_input = input("   ¿Activar gestión de posición basada en tiempo? (s/n) [n]: ").strip().lower() or "n"
        if enable_input in ['s', 'si', 'y', 'yes', 'n', 'no']:
            time_based_tp_enabled = enable_input in ['s', 'si', 'y', 'yes']
            break
        print("   Error: Responda 's' o 'n'")
    
    tp_initial_ticks = 1.0
    tp_degradation_time_minutes = 1.0
    tp_degraded_ticks = 0.5
    tp_break_even_time_minutes = 2.0
    tp_stop_loss_time_minutes = 3.0
    
    if time_based_tp_enabled:
        print("\n   Configuración de degradación progresiva:")
        while True:
            try:
                tp_init_input = input("   TP inicial (ticks) [1.0]: ").strip() or "1.0"
                tp_initial_ticks = float(tp_init_input)
                if tp_initial_ticks >= 0.5:
                    break
                print("   Error: El TP inicial debe ser >= 0.5 ticks")
            except ValueError:
                print("   Error: Ingrese un número válido (puede ser decimal)")
        
        while True:
            try:
                tp_degrade_time_input = input("   Tiempo para degradar TP (minutos) [1.0]: ").strip() or "1.0"
                tp_degradation_time_minutes = float(tp_degrade_time_input)
                if tp_degradation_time_minutes > 0:
                    break
                print("   Error: El tiempo debe ser > 0")
            except ValueError:
                print("   Error: Ingrese un número válido")
        
        while True:
            try:
                tp_degraded_input = input("   TP degradado (ticks) [0.5]: ").strip() or "0.5"
                tp_degraded_ticks = float(tp_degraded_input)
                if tp_degraded_ticks >= 0:
                    break
                print("   Error: El TP degradado debe ser >= 0")
            except ValueError:
                print("   Error: Ingrese un número válido (puede ser decimal)")
        
        while True:
            try:
                tp_be_time_input = input("   Tiempo para break even (minutos) [2.0]: ").strip() or "2.0"
                tp_break_even_time_minutes = float(tp_be_time_input)
                if tp_break_even_time_minutes > tp_degradation_time_minutes:
                    break
                print(f"   Error: El tiempo de break even debe ser > {tp_degradation_time_minutes} min")
            except ValueError:
                print("   Error: Ingrese un número válido")
        
        while True:
            try:
                tp_sl_time_input = input("   Tiempo para aplicar Stop Loss (minutos) [3.0]: ").strip() or "3.0"
                tp_stop_loss_time_minutes = float(tp_sl_time_input)
                if tp_stop_loss_time_minutes > tp_break_even_time_minutes:
                    break
                print(f"   Error: El tiempo de Stop Loss debe ser > {tp_break_even_time_minutes} min")
            except ValueError:
                print("   Error: Ingrese un número válido")
    else:
        print("   Gestión de posición basada en tiempo: DESACTIVADA")
    
    # Precios fijos de salida (opcional)
    print()
    print("   Precios Fijos de Salida: Cerrar automáticamente cuando se alcance un precio específico")
    print("   (Ejemplo: Si compras a $1508.5, puedes salir a $1512.0, $1515.0, etc.)")
    print()
    
    while True:
        usar_precios_fijos = input("   ¿Usar precios fijos de salida? (S/N) [N]: ").strip().upper() or "N"
        if usar_precios_fijos in ["S", "N", "SI", "NO", "Y", "YES"]:
            break
        print("   Error: Ingrese S o N")
    
    fixed_exit_prices = []
    if usar_precios_fijos in ["S", "SI", "Y", "YES"]:
        print("\n   Configure los precios fijos de salida:")
        print("   - Formato: precio,cantidad (ej: 1512.0,1) o solo precio")
        print("   - Sin cantidad o cantidad=0 → cierre completo")
        print("   - Presione Enter sin valor para terminar\n")
        
        def parse_price_input(input_str):
            """Parsea entrada de precio fijo: 'precio' o 'precio,cantidad'"""
            if "," in input_str:
                precio, cantidad = map(str.strip, input_str.split(",", 1))
                return float(precio), int(cantidad) if cantidad else None
            return float(input_str), None
        
        for precio_count in range(1, 11):
            precio_input = input(f"   Precio fijo #{precio_count} [Enter para terminar]: ").strip()
            if not precio_input:
                if precio_count == 1:
                    print("   No se configuraron precios fijos")
                    usar_precios_fijos = "N"
                break
            
            try:
                precio, cantidad = parse_price_input(precio_input)
                if precio <= 0:
                    print("   Error: El precio debe ser > 0")
                    continue
                if cantidad is not None and cantidad < 0:
                    print("   Error: La cantidad debe ser >= 0")
                    continue
                
                fixed_exit_prices.append((precio, cantidad if cantidad else None))
                qty_str = f"{cantidad} contrato(s)" if cantidad else "completo"
                print(f"   Agregado: ${precio:.2f} ({qty_str})")
            except (ValueError, AttributeError):
                print("   Error: Formato inválido. Use: precio o precio,cantidad")
        
        if fixed_exit_prices:
            fixed_exit_prices.sort(key=lambda x: x[0])
            print(f"\n   Configurados {len(fixed_exit_prices)} precio(s) fijo(s):")
            for i, (p, q) in enumerate(fixed_exit_prices, 1):
                print(f"      {i}. ${p:.2f} - {q if q else 'completo'}")
        else:
            usar_precios_fijos = "N"
    
    # ============================================================================
    # 4. CONFIGURACIÓN TÉCNICA
    # ============================================================================
    print("\n[4] CONFIGURACIÓN TÉCNICA")
    print("-" * 80)
    print("   Ajuste el comportamiento de ejecución de órdenes")
    print()
    print("   Tipo de ejecución:")
    print("   1. IMMEDIATE           → Ejecuta inmediatamente al mejor precio disponible")
    print("   2. BID_OFFER_TOUCH     → Espera a que el precio toque el bid/offer")
    print("   3. PRICE_IMPROVEMENT   → Mejora el precio en 1 tick para quedar primero")
    print()
    
    while True:
        trigger_num = input("   Seleccione tipo (1-3) [1]: ").strip() or "1"
        if trigger_num in ["1", "2", "3"]:
            break
        print("   Error: Debe seleccionar 1, 2 o 3")
    
    trigger_map = {"1": "IMMEDIATE", "2": "BID_OFFER_TOUCH", "3": "PRICE_IMPROVEMENT"}
    trigger_type = trigger_map.get(trigger_num, "IMMEDIATE")
    print(f"   Tipo seleccionado: {trigger_type}")
    
    print()
    while True:
        adaptive_speed_num = input("   Velocidad adaptativa? (1=Sí, 2=No) [1]: ").strip() or "1"
        if adaptive_speed_num in ["1", "2"]:
            break
        print("   Error: Debe seleccionar 1 o 2")
    adaptive_speed = (adaptive_speed_num == "1")
    
    while True:
        latency_num = input("   Filtro de latencia? (1=Sí, 2=No) [2]: ").strip() or "2"
        if latency_num in ["1", "2"]:
            break
        print("   Error: Debe seleccionar 1 o 2")
    enable_latency_filter = (latency_num == "1")
    
    while True:
        try:
            timeout_input = input("   Timeout de órdenes (segundos) [60]: ").strip() or "60"
            order_timeout_seconds = int(timeout_input)
            if order_timeout_seconds > 0:
                break
            print("   Error: El timeout debe ser mayor a 0")
        except ValueError:
            print("   Error: Ingrese un número entero válido")
    
    while True:
        try:
            duration_input = input("   Duración total (minutos, 0=infinito) [0]: ").strip() or "0"
            duracion_minutos = int(duration_input)
            if duracion_minutos >= 0:
                break
            print("   Error: La duración debe ser >= 0")
        except ValueError:
            print("   Error: Ingrese un número entero válido")
    
    duracion_segundos = duracion_minutos * 60 if duracion_minutos > 0 else None
    
    print()
    while True:
        plot_live_num = input("   ¿Gráfico de latencia en vivo? (1=Sí, 2=No) [2]: ").strip() or "2"
        if plot_live_num in ["1", "2"]:
            break
        print("   Error: Debe seleccionar 1 o 2")
    plot_latency_live = (plot_live_num == "1")
    
    if plot_latency_live:
        print("   Gráfico en vivo: ACTIVADO (se actualiza cada 10s, no bloquea)")
    else:
        print("   Gráfico en vivo: DESACTIVADO (se guardará al finalizar)")
    
    # ============================================================================
    # 5. VALUACIÓN TEÓRICA (OPCIONAL)
    # ============================================================================
    print("\n[5] VALUACIÓN TEÓRICA (OPCIONAL)")
    print("-" * 80)
    print("   Use modelos de valuación teórica para detectar oportunidades")
    print()
    
    while True:
        use_theo_num = input("   ¿Usar valuación teórica? (1=Sí, 2=No) [2]: ").strip() or "2"
        if use_theo_num in ["1", "2"]:
            break
        print("   Error: Debe seleccionar 1 o 2")
    
    use_theoretical_valuation = (use_theo_num == "1")
    spot_price = None
    risk_free_rate = None
    valuation_model = 'simple'
    domestic_rate = None
    foreign_rate = None
    cheap_threshold_pct = 0.0
    expensive_threshold_pct = 0.0
    days_to_expiry_override = None
    
    if use_theoretical_valuation:
        print("\n   Configure los parámetros de valuación:")
        while True:
            try:
                spot_input = input("   Precio SPOT actual ($): ").strip()
                spot_price = float(spot_input)
                if spot_price > 0:
                    break
                print("   Error: El precio spot debe ser mayor a 0")
            except ValueError:
                print("   Error: Ingrese un número válido")
        
        while True:
            try:
                rate_input = input("   Tasa libre de riesgo anual (% o decimal) [5]: ").strip() or "5"
                risk_free_rate = float(rate_input)
                if risk_free_rate > 100:
                    risk_free_rate = risk_free_rate / 100  # Si es porcentaje
                break
            except ValueError:
                print("   Error: Ingrese un número válido")
        
        print("\n   Modelos disponibles:")
        print("   1. Simple              → Modelo básico")
        print("   2. Continuous          → Compuesto continuo")
        print("   3. Interest Diff       → Diferencia de tasas")
        print("   4. Interest Diff Cont  → Diferencia de tasas (continuo)")
        print()
        
        while True:
            model_num = input("   Seleccione modelo (1-4) [1]: ").strip() or "1"
            if model_num in ["1", "2", "3", "4"]:
                break
            print("   Error: Debe seleccionar 1, 2, 3 o 4")
        
        valuation_model = {"1":"simple","2":"continuous","3":"interest_diff","4":"interest_diff_continuous"}.get(model_num, "simple")
        
        if valuation_model.startswith('interest'):
            while True:
                try:
                    dom_input = input("   Tasa doméstica (%, puede ser decimal) [5]: ").strip() or "5"
                    domestic_rate = float(dom_input)
                    if domestic_rate > 100:
                        domestic_rate = domestic_rate / 100
                    break
                except ValueError:
                    print("   Error: Ingrese un número válido")
            
            while True:
                try:
                    for_input = input("   Tasa extranjera (%, puede ser decimal) [0]: ").strip() or "0"
                    foreign_rate = float(for_input)
                    if foreign_rate > 100:
                        foreign_rate = foreign_rate / 100
                    break
                except ValueError:
                    print("   Error: Ingrese un número válido")
        
        while True:
            try:
                cheap_input = input("   Umbral barato para BUY (% bajo teórico) [0.0]: ").strip() or "0.0"
                cheap_threshold_pct = float(cheap_input)
                break
            except ValueError:
                print("   Error: Ingrese un número válido")
        
        while True:
            try:
                exp_input = input("   Umbral caro para SELL (% sobre teórico) [0.0]: ").strip() or "0.0"
                expensive_threshold_pct = float(exp_input)
                break
            except ValueError:
                print("   Error: Ingrese un número válido")
        
        while True:
            try:
                days_input = input("   Días al vencimiento (aprox) [30]: ").strip() or "30"
                days_to_expiry_override = int(days_input)
                if days_to_expiry_override > 0:
                    break
                print("   Error: Los días deben ser mayor a 0")
            except ValueError:
                print("   Error: Ingrese un número entero válido")
    
    # ============================================================================
    # RESUMEN Y CONFIRMACIÓN
    # ============================================================================
    print("\n" + "="*80)
    print(" "*30 + "RESUMEN DE CONFIGURACIÓN")
    print("="*80)
    print()
    print(f"  Instrumento:     {future_symbol}")
    print(f"  Tick Size:       ${tick_size:.2f}")
    print(f"  Cantidad:        {order_quantity} contrato(s)")
    print()
    
    if entry_side == 'BUY':
        print(f"  Estrategia:      COMPRAR cuando precio <= ${entry_max_price:.2f}")
    else:
        print(f"  Estrategia:      VENDER cuando precio >= ${entry_min_price:.2f}")
    
    print()
    print(f"  Salidas:")
    print(f"    • Take Profit:  {target_profit_ticks} ticks")
    print(f"    • Stop Loss:    {target_stop_loss_ticks} ticks")
    if target_time_exit_minutes:
        print(f"    • Time Exit:    {target_time_exit_minutes} minutos")
    else:
        print(f"    • Time Exit:    Desactivado")
    
    if time_based_tp_enabled:
        print(f"    • Gestión TP basada en tiempo: ACTIVADA")
        print(f"      - TP inicial: {tp_initial_ticks} ticks (0-{tp_degradation_time_minutes} min)")
        print(f"      - TP degradado: {tp_degraded_ticks} ticks ({tp_degradation_time_minutes}-{tp_break_even_time_minutes} min)")
        print(f"      - Break even: {tp_break_even_time_minutes}-{tp_stop_loss_time_minutes} min")
        print(f"      - Stop Loss: {tp_stop_loss_time_minutes}+ min")
    else:
        print(f"    • Gestión TP basada en tiempo: DESACTIVADA")
    
    if fixed_exit_prices and len(fixed_exit_prices) > 0:
        print(f"    • Precios Fijos: {len(fixed_exit_prices)} precio(s) configurado(s)")
        for i, (precio, cantidad) in enumerate(fixed_exit_prices, 1):
            qty_str = f"{cantidad} contrato(s)" if cantidad else "completo"
            print(f"      - ${precio:.2f} ({qty_str})")
    else:
        print(f"    • Precios Fijos: Desactivado")
    
    print()
    print(f"  Técnica:")
    print(f"    • Tipo ejecución:  {trigger_type}")
    print(f"    • Velocidad adapt:  {'Sí' if adaptive_speed else 'No'}")
    print(f"    • Filtro latencia: {'Sí' if enable_latency_filter else 'No'}")
    print(f"    • Timeout órdenes:  {order_timeout_seconds}s")
    
    if duracion_minutos > 0:
        print(f"    • Duración total: {duracion_minutos} minutos")
    else:
        print(f"    • Duración total: Infinito")
    
    if use_theoretical_valuation:
        print()
        print(f"  Valuación teórica: ACTIVADA")
        print(f"    • Modelo: {valuation_model}")
        print(f"    • Spot: ${spot_price:.2f}")
    
    print()
    print("="*80)
    
    while True:
        confirmar = input("\n   ¿Desea iniciar el bot con esta configuración? (S/N) [S]: ").strip().upper() or "S"
        if confirmar in ["S", "N", "SI", "NO", "Y", "YES"]:
            break
        print("   Error: Ingrese S o N")
    
    if confirmar in ["N", "NO"]:
        print("\n   [CANCELADO] Configuración no guardada.")
        return
    
    # Crear configuración
    config = {
        'future_symbol': future_symbol,
        'tick_size': tick_size,
        'order_quantity': order_quantity,
        'entry_side': entry_side,
        'entry_max_price': entry_max_price,
        'entry_min_price': entry_min_price,
        'target_profit_ticks': target_profit_ticks,
        'target_stop_loss_ticks': target_stop_loss_ticks,
        'target_time_exit_minutes': target_time_exit_minutes,
        'fixed_exit_prices': fixed_exit_prices,  # Precios fijos de salida
        'trigger_type': trigger_type,
        'adaptive_speed': adaptive_speed,
        'enable_latency_filter': enable_latency_filter,
        'order_timeout_seconds': order_timeout_seconds,
        'filter_market_hours_only': True,
        'filter_max_data_age_seconds': 5,
        'plot_latency_live': plot_latency_live,
        # Gestión de posición basada en tiempo (TP degradado)
        'time_based_tp_enabled': time_based_tp_enabled,
        'tp_initial_ticks': tp_initial_ticks,
        'tp_degradation_time_minutes': tp_degradation_time_minutes,
        'tp_degraded_ticks': tp_degraded_ticks,
        'tp_break_even_time_minutes': tp_break_even_time_minutes,
        'tp_stop_loss_time_minutes': tp_stop_loss_time_minutes
    }
    
    if use_theoretical_valuation:
        config.update({
            'use_theoretical_valuation': True,
            'spot_price': spot_price,
            'risk_free_rate': risk_free_rate,
            'valuation_model': valuation_model,
            'domestic_rate': domestic_rate,
            'foreign_rate': foreign_rate,
            'cheap_threshold_pct': cheap_threshold_pct,
            'expensive_threshold_pct': expensive_threshold_pct,
            'days_to_expiry_override': days_to_expiry_override,
        })
    
    # Crear bot
    print()
    print("="*70)
    print("[START] INICIANDO BOT...")
    print("="*70)
    print()
    
    bot = PriceBasedBot(config)
    
    # Inicializar
    if bot.initialize():
        print()
        print("="*70)
        print("[OK] BOT INICIALIZADO CORRECTAMENTE")
        print("="*70)
        print()
        print("[INFO] Presiona Ctrl+C para detener el bot en cualquier momento")
        print()
        
        # Ejecutar
        bot.run(duration=duracion_segundos)
    else:
        print("[ERROR] No se pudo inicializar el bot")

if __name__ == "__main__":
    main()


