# Skrillex

Independent experimental deterministic threshold-graph x86 runtime for Nintendo Switch. No Wine, Latitude, Box64 or installed title launcher. R06 is a PE32 loader and limited instruction interpreter, not a working game runtime. Win32 imports and D3D9 remain unimplemented. The game is not distributed with this repository.

Target: `sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe`. The NRO logs executed instructions and stops at unsupported instructions. Build with devkitPro/libnx.

R06 host trace: 39 guest instructions; first unresolved import KERNEL32.dll!GetVersionExA. R05 physical Switch: 27 instructions. R06 hardware result is not yet verified. Threshold graphs implement integer add/subtract/XOR; multiplication and division currently use native C arithmetic, not synthesized graphs.
