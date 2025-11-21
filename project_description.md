# BSc Project Description: Compiler and Verifier Reliability and Testing 2025/6

## BSc Project: *Trust Me, I am a Verifier! (Or Should You?)*
### Proof Assistant Reliability and Testing
**Project supervisors:** Dr Mohammad Ahmad Abdulaziz Ali Mansour, Dr Karine Even Mendoza

A proof assistant is a program that checks whether a mathematical proof is correct. Proof assistants are widely used, ranging from practical software verification—such as verifying a Linux kernel [1], a C compiler [2], or cryptographic software by Apple [3] and AWS [4]—to high-level mathematical results like the formalization of Fermat’s Last Theorem [5].

In software verification, a proof assistant checks that a program behaves exactly as intended: no bugs, no hidden behaviours, no surprises.

However, proof assistants depend on an entire **software stack**—frontends, compilers, interfaces, external solvers, etc. Even if the core is correct, surrounding software may contain bugs affecting reliability. These bugs include (from most to least severe):

### Types of Reliability Problems
- **False negatives**  
  Undetected violations of the specification → buggy software is marked “correct”.
- **False positives**  
  Correct software is rejected → wasted time and developer confusion.
- **Crashes**  
  Internal errors stopping the verifier/compiler.
- **Hangs**  
  Infinite loops or non-terminating behaviour.

## Project Scope

You will test part of the software stack of the widely used proof assistant **Isabelle/HOL** [6], which has verified systems like the seL4 OS Kernel [1] and is used in industry (Apple, Amazon).

The project exposes you to **logic, formal methods, compilers, PL, and fuzzing**.

You must select:
1. A target component in the Isabelle/HOL toolchain.
2. A fuzzing method.
3. A design for a *new* fuzzer or a significant extension to an existing one (e.g., AFL1 modifications).

Likely bug-prone areas:
- Frontend
- Interfaces between Isabelle/HOL and external tools
- Compiler that builds Isabelle/HOL (PolyML)

(Modules relevant: logic/theory, compilers, software engineering.)

## Fuzzing Requirements

You must build or significantly extend a fuzzer, for example:
- Write new code mutation operators for AFL
- Extend AFL++, LibFuzzer, etc.

Resources:
- AFL technical whitepaper  
  https://lcamtuf.coredump.cx/afl/technical_details.txt
- AFL dictionaries  
  https://github.com/google/AFL/blob/master/dictionaries/README.dictionaries
- AFL++  
  https://aflplus.plus
- LibFuzzer  
  https://llvm.org/docs/LibFuzzer.html

## What Your Evaluation Must Include

- A **manual** explaining how to build and instrument the verifier/compiler from source
- Test generation campaign to discover new bugs
- Code coverage comparison (baseline vs your tool)
- Throughput comparison vs existing tools
- Additional analyses as needed

## Project Variants (Choose One)

Each student must pick a **unique** variant:

1. **PolyML compiler** (compiles Isabelle/HOL)  
   → crashes, miscompilation bugs.
2. **Isabelle GUI frontend**  
   → crashes, hangs.
3. **Isabelle ↔ external provers** (Sledgehammer interfaces)  
   → integration bugs.
4. **Isabelle’s unifier** (trusted core component)  
   → false positives/negatives.
5. **Software verified by Isabelle/HOL** (e.g., seL4)  
   → bugs in interfaces/specs.
6. **Your own variant** involving other theorem provers (see resources).

### Requirements for Environment
- Must run Docker or a VM
- Familiarity with Unix, Ninja, CMake
- GitHub account required
- May apply for free AWS EC2 access (if unused)  
  https://aws.amazon.com/free/

## Deliverables

**Mandatory final report**, including:
- Architecture of your chosen SUT
- Methodology
- Implementation details and instrumentation steps
- Test generation method
- Evaluation results
- Bug reports

**Plus uploads to KEATS:**
1. Final report
2. Zip/tar of your source code
3. Appendix (printout of all code)
4. Presentation (must be <10 minutes; recommended 9–9.55 minutes)

You are **encouraged** to upload artefacts to Zenodo or figshare, including dataset creation.

## References

[1] Klein et al. *seL4: Formal verification of an OS kernel*, SOSP 2009.  
[2] Leroy, X. *Formal verification of a realistic compiler*, CACM 2009.  
https://doi.org/10.1145/1538788.1538814  
[3] Apple Security Guide  
https://support.apple.com/en-gb/guide/security/sec59b0b31ff/web  
[4] AWS AutoCorrode  
https://github.com/awslabs/AutoCorrode  
[5] FLT formal proof announcement  
https://leanprover-community.github.io/blog/posts/FLT-announcement/  
[6] Isabelle/HOL reference  
https://doi.org/10.1007/3-540-45949-9

## Additional Resources

| Name | Git Repository |
|------|----------------|
| Coq / rocq | https://github.com/rocq-prover/rocq |
| Isabelle | https://isabelle.in.tum.de/dist/Isabelle2025_linux.tar.gz |
| Lean | https://github.com/leanprover/lean4 |
| HOL4 | https://github.com/HOL-Theorem-Prover/HOL |
| PolyML | https://github.com/polyml |
