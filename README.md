# Skrillex

Independent experimental deterministic threshold-graph x86 runtime for Nintendo Switch. No Wine, Latitude, Box64 or installed-title launcher. The game is not distributed with this repository.

## R32

PE32 loader, guest memory, stack, TEB, isolated heap, import table with synthetic dispatch tokens, partial x86 integer interpreter and partial Win32 process services. Threshold graphs implement integer add/subtract/XOR; multiplication, division, and other operations still use native C arithmetic. Not a full neural implementation of Windows.

Target: `sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe`. Build with devkitPro/libnx. The NRO logs executed instructions and stops at unsupported operations. Log: `sdmc:/switch/Skrillex-R32.log`.

Last verified GTA host trace: R28, 16454 guest instructions, 77 API calls, 214 bound import tokens (not 214 implemented APIs). R28 stopped at x86 BSR (0F BD), implemented in R29. R29–R32 GTA trace has not been verified. Physical hardware confirmed through R16 (2202 instructions, 43 calls).

Limitations: simulated XP-compatible process environment, single-thread critical sections and TLS, fixed 8 MiB guest heap, limited CP1252 and Latin case mapping/classification, no full file system, DLL loader, Direct3D, audio, or full x86 support. Host trace is not a proof of Windows semantic equivalence or game playability. Unknown functions stop execution.

R32 expands width-aware shifts/rotates and 16-bit stack and ALU instructions. CI now compiles public synthetic fixtures and runs ASan/UBSan before generating the ARM64 NRO. Results must be checked before claiming a verified build. The x87 model uses binary64, not full extended precision; SSE and graphics are not implemented.

R32 adds a virtual KERNEL32 module identity and a registry of 75 named API entry points (partial semantics), with LoadLibrary A/W, GetModuleHandle A/W, GetProcAddress and FreeLibrary. Unsupported DLLs/exports fail explicitly; no host DLL loading. A synthetic regression covers direct and thunk calls, stable tokens and failure paths. No USER32 window or D3D9 implementation yet.

R32 introduces an ANSI USER32 model: class registration, virtual top-level window creation with execution of guest WM_NCCREATE/WM_CREATE callbacks, rectangles, and a bounded message queue with guest DispatchMessage. No real host window, renderer, input, child windows, menus or D3D9. A public synthetic fixture checks WndProc execution, message dispatch and rejected creation; results are not yet verified. The last actual GTA trace remains R28.
