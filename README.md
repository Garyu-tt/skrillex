# Skrillex

Independent experimental deterministic threshold-graph x86 runtime for Nintendo Switch. No Wine, Latitude, Box64 or installed-title launcher. The game is not distributed with this repository.

## R39

PE32 loader, guest memory, stack, TEB, isolated heap, import table with synthetic dispatch tokens, partial x86 integer interpreter and partial Win32 process services. Threshold graphs implement integer add/subtract/XOR; multiplication, division, and other operations still use native C arithmetic. Not a full neural implementation of Windows.

Target: `sdmc:/games/Grand Theft Auto San Andreas/gta_sa.exe`. Build with devkitPro/libnx. The NRO logs executed instructions and stops at unsupported operations. Log: `sdmc:/switch/Skrillex-R39.log`.

Last verified GTA host trace: R28, 16454 guest instructions, 77 API calls, 214 bound import tokens (not 214 implemented APIs). R28 stopped at x86 BSR (0F BD), implemented in R29. R29–R39 GTA trace has not been verified. Physical hardware confirmed through R16 (2202 instructions, 43 calls).

Limitations: simulated XP-compatible process environment, single-thread critical sections and TLS, fixed 8 MiB guest heap, limited CP1252 and Latin case mapping/classification, no full file system, DLL loader, Direct3D, audio, or full x86 support. Host trace is not a proof of Windows semantic equivalence or game playability. Unknown functions stop execution.

R30 expands width-aware shifts/rotates and 16-bit stack and ALU instructions. CI now compiles public synthetic fixtures and runs ASan/UBSan before generating the ARM64 NRO. Results must be checked before claiming a verified build. The x87 model uses binary64, not full extended precision; SSE and graphics are not implemented.

R31 adds a virtual KERNEL32 module identity and a registry of 75 named API entry points (partial semantics), with LoadLibrary A/W, GetModuleHandle A/W, GetProcAddress and FreeLibrary. Unsupported DLLs/exports fail explicitly; no host DLL loading. A synthetic regression covers direct and thunk calls, stable tokens and failure paths. No D3D9 implementation yet.

R32 introduces an ANSI USER32 model: class registration, virtual top-level window creation with execution of guest WM_NCCREATE/WM_CREATE callbacks, rectangles, and a bounded message queue with guest DispatchMessage. No real host window, renderer, input, child windows, menus or D3D9. A public synthetic fixture checks WndProc execution, message dispatch and rejected creation; results are not yet verified. The last actual GTA trace remains R28.

R33 adds a read-only game resource filesystem rooted at the Switch game directory. Supports CreateFile A/W (read-only OPEN_EXISTING), ReadFile, file size, seek, close, file type and limited attributes/current directory. Rejects parent traversal, other drives, device names and write/create requests. Host access to real resources is disabled; the host fixture uses a temporary synthetic stream. Limits: 64 open files, 1 MiB per read, ASCII names, no directory enumeration, no asynchronous IO, no full Windows sharing semantics.

R34 retains the final 32 executed instructions and register state for diagnosis. R33–R34 fixtures and builds are not yet verified; no new GTA execution count is claimed.

R35 adds an experimental D3D9 COM interface: Direct3DCreate9, guest vtables, one windowed CPU reference device (up to 1920x1080), color-only Clear, BeginScene/EndScene, Present with FNV-1a checksum, and reference counting. Present hashes pixels but does not display them. No drawing, shaders, depth buffer, texture support, native GPU or full COM compatibility. Unsupported methods stop; unsupported device configurations return an error. The synthetic fixture expects 0x91193335 from a 4x3 buffer cleared to 0xff123456; execution is not yet verified. This is not a GTA-rendered frame.

R36 adds SetFVF/GetFVF and DrawPrimitiveUP for pretransformed XYZRHW+diffuse (0x44) vertices, triangle lists/strips/fans, fixed-point edge tests and interpolated ARGB. Reference subset requires rhw=1, no depth, blending, culling or texture sampling. The synthetic 4x3 triangle fixture expects six changed pixels and FNV-1a 0x3d35d94d; not yet executed. No actual GTA frame or screen presentation is verified.

R37 adds optional D16 auto-depth buffer, fixed-point depth interpolation, all eight Z comparisons, ZENABLE/ZWRITEENABLE/ZFUNC and color/depth clear. No stencil or other depth formats. Fixture covers overlapping near/far triangles, depth-write masking and depth-only clear.

R38 adds guest vertex buffer COM objects (32 live, up to 2 MiB each within the 8 MiB guest heap), Lock/Unlock, GetDesc, stream 0 binding, stream lookup and non-indexed DrawPrimitive. Only XYZRHW+diffuse and restricted usage/pool/lock flags; explicit unbind/release before final device release. Index buffers, textures, transform pipeline and Maxwell presentation remain unimplemented. Fixtures for R37–R38 have not yet been executed; last verified GTA trace remains R28.

R39 adds guest INDEX16/INDEX32 buffers, Lock/Unlock/GetDesc, SetIndices/GetIndices, and DrawIndexedPrimitive for triangle lists/strips/fans. Validates the signed base vertex, declared index range, buffer bounds and all vertices before drawing; shared vertices remain in guest memory. Up to 32 live index buffers (2 MiB maximum each, subject to shared 8 MiB heap). This reference path expands the indexed draw into a temporary vertex array; not a GPU cache or measured speedup. Synthetic regression covers both formats, negative BaseVertexIndex and invalid ranges. Build and regression results remain unverified. Textures and native screen presentation remain absent.
