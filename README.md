# NeroExec

Independent experimental deterministic threshold-graph x86 runtime for Nintendo Switch. No Wine, Latitude, Box64 or installed title launcher. R03 is a PE32 loader and limited instruction interpreter, not a working game runtime. Win32 imports and D3D9 remain unimplemented. The game is not distributed with this repository.

Target: `sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe`. The NRO logs executed instructions and stops at unsupported instructions. Build with devkitPro/libnx.
