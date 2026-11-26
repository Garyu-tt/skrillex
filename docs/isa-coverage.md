# Skrillex ISA Complete — initial inventory (R49 candidate)

Goal: implement user-mode IA-32 semantics on ARM64 first, then Intel64. Proton/Wine are API references, not CPU instruction sources. No mandatory dependency on Wine, Box64 or FEX. Consult Intel SDM vol. 2 and Intel XED data (https://github.com/intelxed/xed) for the encoding inventory. This initial family matrix is manual, not an imported XED database or a numerical coverage measurement.

| Family | R48 accepted baseline / R49 candidate | Remaining scope |
|---|---|---|
| Integer ALU | Partial: ADD/ADC/SUB/SBB/CMP/AND/OR/XOR/TEST/INC/DEC/NEG/NOT | Audit encodings, defined flags, faults, widths |
| Data transfer | Partial MOV/MOVZX/MOVSX/LEA/XCHG/BSWAP | Segment forms, 16-bit variants, address-size prefix, far forms; POP r/m candidate R52 |
| Multiply/divide | 8/16/32-bit MUL/IMUL/DIV/IDIV candidate R50 | Architectural exception delivery, complete operand/prefix audit |
| Shifts/rotates | Partial 8/16/32-bit group 2 | SHLD/SHRD 16/32 candidate R51; defined flags audit |
| Bit manipulation | Partial BT/BTS/BTR/BTC/BSF/BSR | 16-bit forms and LOCK memory modification candidate R51; audit encoding and prefix legality |
| Atomic RMW | XADD partial in R48; CMPXCHG candidate R49 | CMPXCHG8B candidate R51; other valid LOCK forms, memory model, thread scheduler |
| Branch/call/stack | Partial Jcc/JMP/CALL/RET/LOOP/CMOV/SETcc/PUSH/POP | Operand/address sizes, ENTER, far transfers, exceptions; PUSH/POP r/m expanded R52 |
| Strings | Partial MOVS/CMPS/STOS/LODS/SCAS and REP | Address size, restart semantics, segment handling |
| Legacy adjust | Not audited | AAA/AAS/DAA/DAS/AAM/AAD |
| x87 | Partial host double reference | 80-bit precision, control/status, exceptions, instruction set |
| MMX | Not implemented | Register aliasing with x87, packed arithmetic, EMMS |
| SSE/SSE2 | Not implemented | XMM state, MXCSR, moves, arithmetic, conversions, exceptions |
| SSE3–SSE4.2 | Not implemented | Prefix maps, feature-specific instructions |
| AVX/AVX2/FMA | Not implemented | VEX decoder, YMM state, feature gating |
| Other extensions | Not implemented | BMI, AES, SHA, AVX-512, etc., as applicable |
| CPUID/TSC | Partial; synthetic deterministic time | Feature contract, serialization, extended leaves |
| System/privileged | Unsupported unless explicit virtual contract | Correct guest fault/OS mediation; never silently execute privileged host operations |
| Intel64 | Not implemented | PE32+, REX, 64-bit regs/addressing, ABI, unwind, RIP relative |

## Acceptance contract
- Track encoding, prefix, operand width, addressing, architectural result, defined flags, exception and memory semantics individually.
- States: missing, partial, implemented-unverified, verified (specific fixture only), unsupported-by-design (with explicit guest fault).
- Do not advertise CPUID features before implementing their required contract.
- Use independently generated synthetic instruction fixtures; compare to native x86 where possible. Do not use proprietary game data in CI.
- Require strict C11 regression, ASan/UBSan, ARM64 NRO build and artifact publication on PR. Hardware tests are a separate gate.
- Single-thread LOCK behavior is not a multiprocessor guarantee.
- Use the existing graph ALU for scalar arithmetic where available; native floating point and integer multiply/divide are currently hybrid reference paths, not a fully neural executor.
- Next batch: SHLD/SHRD, missing data-transfer forms; then audit prefix decoder and implement MMX/SSE register state.
