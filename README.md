# Skrillex

Independent experimental deterministic threshold-graph x86 runtime for Nintendo Switch. No Wine, Latitude, Box64 or installed-title launcher. The game is not distributed with this repository.

## R30

PE32 loader, guest memory, stack, TEB, isolated heap, import table with synthetic dispatch tokens, partial x86 integer interpreter and partial Win32 process services. Threshold graphs implement integer add/subtract/XOR; multiplication, division, and other operations still use native C arithmetic. Not a full neural implementation of Windows.

Target: `sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe`. Build with devkitPro/libnx. The NRO logs executed instructions and stops at unsupported operations. Log: `sdmc:/switch/Skrillex-R30.log`.

Last verified GTA host trace: R28, 16454 guest instructions, 77 API calls, 214 bound import tokens (not 214 implemented APIs). R28 stopped at x86 BSR (0F BD), implemented in R29. R29–R30 GTA trace has not been verified. Physical hardware confirmed through R16 (2202 instructions, 43 calls).

Limitations: simulated XP-compatible process environment, single-thread critical sections and TLS, fixed 8 MiB guest heap, limited CP1252 and Latin case mapping/classification, no full file system, DLL loader, Direct3D, audio, or full x86 support. Host trace is not a proof of Windows semantic equivalence or game playability. Unknown functions stop execution.

R30 expands width-aware shifts/rotates and 16-bit stack and ALU instructions. CI now compiles public synthetic fixtures and runs ASan/UBSan before generating the ARM64 NRO. Results must be checked before claiming a verified build. The x87 model uses binary64, not full extended precision; SSE and graphics are not implemented.
