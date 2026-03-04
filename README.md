# 🏭 Price-Based Futures Bot — Production Build (Primary API / Matba Rofex)

> Production-certified, instrument-agnostic algorithmic trading bot for Argentine futures markets. Homologated for live execution with extended risk controls, latency calibration, operation limits, and granular order management.

---

## 🇬🇧 English

### What it is

`HOMOLOGADOproduccion1.py` is the **production-certified evolution** of a price-based futures OMS. Unlike instrument-specific implementations, this build is fully configurable at runtime — no hardcoded defaults for any single asset.

It was built to be deployed across multiple futures instruments (DLR, GGAL, GFGC, etc.) without code changes.

### What makes it different from a standard price bot

| Feature | Standard bot | This build |
|---|---|---|
| Instrument | Hardcoded | Runtime input |
| Operation limits | None | Per-day + total cap |
| Price improvement | Repeated | Once per order (configurable) |
| Latency filter | Optional | 5-min calibration window |
| Latency dashboard | No | Live matplotlib plot |
| Book depth filter | Basic | `depth_levels_to_track` + `min_depth_contracts` |
| Order type | Fixed | `DAY` / `LIMIT` / configurable |
| TimeInForce | Fixed | Configurable per run |
| API timeout | Default | Configurable |

### Core strategy

Pure **price-level execution** — instrument-agnostic:

```
Entry (BUY):  last ≤ entry_max_price → limit order at (price − improvement_ticks)
Entry (SELL): last ≥ entry_min_price → limit order at (price + improvement_ticks)

Exit priority:
  1. Fixed price exits (partial fills at multiple levels)
  2. Take Profit (ticks from fill)
  3. Stop Loss (ticks from fill)
  4. Time-based TP degradation (aging management)
  5. Hard time exit
```

### Production-specific features

**Operation caps**
```python
max_operations_per_day = 10    # Resets at midnight
max_operations_total   = 50    # Hard lifetime cap
```

**Latency calibration (5-minute warmup)**
- Measures baseline latency mean and std from WebSocket feed
- Only enables execution after calibration is complete
- Rejects orders when `latency > baseline × max_latency_multiplier`
- Live latency dashboard via matplotlib (`plot_latency_live`)

**Price improvement control**
```python
allow_price_improvement_once = True  # Improves tick position only once per order
```
Prevents the bot from continuously chasing the book and accumulating market impact.

**Granular book depth filter**
```python
depth_levels_to_track  = 5    # Track N levels of L2
min_depth_contracts    = 3    # Minimum contracts at best bid/offer to fire
```

**Configurable order semantics**
```python
time_in_force = 'DAY'    # or 'IOC', 'FOK', 'GTC'
order_type    = 'LIMIT'  # or 'MARKET'
```

### Theoretical valuation models (optional entry gate)

| Model | Formula |
|---|---|
| `simple` | `F* = S × (1 + r × T)` |
| `continuous` | `F* = S × e^(r × T)` |
| `interest_diff` | `F* = S × (1 + r_dom × T) / (1 + r_for × T)` |
| `interest_diff_continuous` | `F* = S × e^((r_dom − r_for) × T)` |

Entry fires only if market is sufficiently cheap (BUY) or expensive (SELL) vs theoretical.

### Requirements

```bash
pip install pyRofex python-dotenv numpy matplotlib
```

### Configuration (`.env`)

```
PRIMARY_USERNAME=your_user
PRIMARY_PASSWORD=your_password
PRIMARY_ACCOUNT=your_account
```

### Skills demonstrated

- Production-grade OMS design: instrument-agnostic, runtime-configurable
- Latency measurement, calibration, and execution gating
- Operation frequency controls (daily + lifetime caps)
- Granular L2 book depth filtering
- Price improvement discipline (once-per-order)
- Multi-model theoretical valuation (simple, continuous, interest differential)
- Time-based TP degradation (position aging management)
- Partial exit management at multiple fixed price levels
- Order lifecycle: NEW → FILLED / CANCELLED / REJECTED with auto-cancel on timeout
- Live latency and P&L dashboards via matplotlib

---

## 🇦🇷 Español

### Qué es

`HOMOLOGADOproduccion1.py` es la **versión productiva certificada** de un OMS price-based para futuros. A diferencia de implementaciones específicas por instrumento, este build es 100% configurable en runtime — sin defaults hardcodeados para ningún activo en particular.

Diseñado para desplegarse sobre múltiples futuros (DLR, GGAL, GFGC, etc.) sin modificar código.

### Diferencias clave respecto a un bot estándar

- **Límites de operaciones:** tope diario y total configurable — esencial en producción
- **Mejora de precio única:** evita perseguir el book repetidamente con la misma orden
- **Calibración de latencia:** ventana de 5 minutos antes de habilitar ejecución
- **Dashboard de latencia en vivo:** detección de degradación de feed en tiempo real
- **Filtro de profundidad de book:** exige mínimo de contratos en bid/offer antes de disparar
- **Semántica de orden configurable:** TimeInForce y OrderType como parámetros de entrada

### Modelos de valuación teórica (opcional)

| Modelo | Fórmula |
|---|---|
| `simple` | `F* = S × (1 + r × T)` |
| `continuous` | `F* = S × e^(r × T)` |
| `interest_diff` | `F* = S × (1 + r_dom × T) / (1 + r_for × T)` |
| `interest_diff_continuous` | `F* = S × e^((r_dom − r_for) × T)` |

### Skills que demuestra

- Diseño de OMS productivo: agnóstico de instrumento, configurable en runtime
- Medición de latencia, calibración y gate de ejecución
- Control de frecuencia de operaciones (diario + lifetime)
- Filtrado granular de profundidad de book L2
- Disciplina de mejora de precio (una vez por orden)
- Valuación teórica multi-modelo (simple, continuo, diferencial de tasas)
- TP degradado por tiempo (gestión del aging de posición)
- Salidas parciales en múltiples precios fijos
- Ciclo de vida completo de órdenes con auto-cancel por timeout
- Dashboards de latencia y P&L en tiempo real con matplotlib

---

## Author
**Galo Szlomowicz** · [github.com/GaloSzlomowicz](https://github.com/GaloSzlomowicz)

## License
This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
> *Production-certified futures OMS — instrument-agnostic, latency-calibrated, operation-capped. Built for live execution on Matba Rofex via Primary API.*
