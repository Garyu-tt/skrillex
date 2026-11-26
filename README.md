# Skrillex

Independent experimental deterministic threshold-graph x86 runtime for Nintendo Switch. No Wine, Latitude, Box64 or installed-title launcher. The game is not distributed with this repository.

## R16

PE32 loader, guest memory, stack, TEB, isolated heap, import table with synthetic dispatch tokens, partial x86 integer interpreter and partial Win32 process services. Threshold graphs implement integer add/subtract/XOR; multiplication, division, and other operations still use native C arithmetic. Not a full neural implementation of Windows.

Target: `sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe`. Build with devkitPro/libnx. The NRO logs executed instructions and stops at unsupported operations. Log: `sdmc:/switch/Skrillex-R16.log`.

Host trace on a locally held game copy: 2202 guest instructions, 43 API calls, 214 PE imports bound to dispatch tokens (not 214 implemented APIs). Stops at KERNEL32.dll!GetCPInfo. ALU selftest passed 3072 arithmetic and 65536 byte comparison cases plus flag checks. Physical hardware previously verified R03–R05; R16 not yet verified on Switch.

Limitations: simulated XP-compatible process environment, single-thread critical sections and TLS, fixed 8 MiB guest heap, CP1252 only, no full file system, DLL loader, Direct3D, audio, or full x86 support. Host trace is not a proof of Windows semantic equivalence or game playability. Unknown functions stop execution.
