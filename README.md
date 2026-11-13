# Lean 4 checks for semistable 1-motives

This repository accompanies **Semistable 1-motives: monodromy, explicit periods, and local duality**, by Mohammadreza Mohajer. It contains Lean 4 formalizations of selected algebraic identities and finite computations appearing in the manuscript.

Lean **4.19.0** successfully checked all **nine theorem declarations**, with compiler exit code **0**. The recorded check was completed on 12 November 2026 in Atlantic time; the machine-readable timestamps are in UTC. The original compiler output and run metadata are provided in [`results/`](results/).

## Reproduce the check

1. Download or clone this repository and open a terminal in its root directory.
2. Install Lean using the [official installation guide](https://lean-lang.org/install/). The [`lean-toolchain`](lean-toolchain) file specifies `leanprover/lean4:v4.19.0`. With the Elan version manager installed, running Lean from this directory selects that version.
3. Run:

```text
lean --version
lean -o AppendixChecks.olean AppendixChecks.lean
```

The first command should report version `4.19.0`. The second command checks every declaration and prints nine axiom reports. A successful run exits with code `0` and reports no Lean errors. The source imports only `Std`, which is included in the Lean distribution. Mathlib and external datasets are not required.

An optional Python 3 wrapper records a fresh run in `.build/latest/`:

```text
python verify.py
```

Use `python3 verify.py` if that is the Python command on your system. If Lean is not on PATH, supply the executable explicitly:

```text
python verify.py --lean "C:\path\to\lean.exe"
```

The wrapper checks the compiler version, exit code, theorem names, and axiom reports, then saves the fresh output and metadata. It uses only Python's standard library. Lean performs the proof checking; Python runs the command and records its result. The files in `results/` retain the original verification record.

## Input and recorded output

| File | Purpose |
| --- | --- |
| [`AppendixChecks.lean`](AppendixChecks.lean) | Complete input: definitions, hypotheses, matrices, finite computations, nine theorem statements and proofs, and nine `#print axioms` commands. |
| [`lean-toolchain`](lean-toolchain) | Specifies Lean 4.19.0. |
| [`results/lean_version.txt`](results/lean_version.txt) | Compiler version, platform, and commit identifier from the recorded run. |
| [`results/lean_output.txt`](results/lean_output.txt) | Original compiler output, including every axiom report. |
| [`results/lean_run_status.json`](results/lean_run_status.json) | Original run status, UTC timestamps, command, exit code, theorem names, source hashes, and axiom reports. |
| [`results/checks.csv`](results/checks.csv) | A compact table of the nine checked statements and their dependencies. |
| [`verify.py`](verify.py) | Optional wrapper for reproducing the check and recording fresh evidence. |
| [`SHA256SUMS`](SHA256SUMS) | SHA-256 hashes of the distributed source, documentation, and verification records. |
| [`CITATION.cff`](CITATION.cff) | Citation metadata for this computational supplement. |

The input matrices, residue ranges, and expected values are defined directly in `AppendixChecks.lean`. The proof terms are checked when Lean compiles that file. The `.olean` file produced by compilation is a generated artifact and can be recreated from the source.

## What the nine declarations establish

| Declaration | Mathematical content | Manuscript reference |
| --- | --- | --- |
| `reduced_differential_square_zero` | The composite of the two defined differentials is zero, for arbitrary types and operations satisfying the explicit subtraction and commutation hypotheses. | `eq:mixed-reduced`, `eq:reducedcomplex`; the algebraic template applies to `eq:cst`. |
| `scalar_block_trace` | The stated block trace identity holds for arbitrary integer entries in the scalar-block specialization. | Scalar specialization of `eq:blockpair`. |
| `concrete_dual_matrices_are_trace_zero` | Each of the eight specified integer matrices has trace zero. | `ex:three`. |
| `concrete_projective_dual_pairing` | The 64 specified trace pairings form the eight-by-eight identity matrix. | `ex:three`; the matrix calculation in `eq:integraltrace`. |
| `concrete_self_gram_matrix` | The trace pairings of the eight trace-zero matrices give the displayed Gram matrix. | `ex:three`, `prop:tracedefect`. |
| `concrete_self_trace_determinant` | Cofactor expansion of this concrete Gram matrix gives determinant **-3**, hence absolute value **3**. | The rank-three example in `prop:tracedefect`. |
| `elliptic_affine_point_count` | There are **8** pairs of residues satisfying `y^2 = x^3 + x + 1` modulo **5**. | `ex:mixedelliptic`. |
| `elliptic_projective_point_count` | The defined affine count plus one is **9**. The geometric identification of the extra point is supplied by the manuscript. | `ex:mixedelliptic`. |
| `elliptic_frobenius_trace` | The integer calculation `5 + 1 - 9 = -3` holds. | `ex:mixedelliptic`. |

The manuscript references are LaTeX labels retained from the formalization draft's scope table. They identify the intended calculations and remain meaningful if the displayed equation or example numbers change. Lean checks the formal statements in the source file; the correspondence with the manuscript is explained by these descriptions.

## Reading the axiom reports

The final nine commands in `AppendixChecks.lean` report the logical dependencies of the theorem declarations:

- Four declarations do not depend on any axioms.
- Five declarations depend only on `propext`, Lean's standard propositional extensionality axiom.

The source contains no `sorry` or `admit` proof placeholders and declares no additional axioms. No theorem depends on `sorryAx`. The finite computations use `decide`, which constructs proofs checked by Lean's kernel. No `native_decide` tactic is used.

The subtraction and commutation assumptions in `ReducedData` are explicit hypotheses of the differential calculation. Readers can inspect those assumptions directly in the source.

## Relation to the manuscript

These formalizations verify the nine statements listed above. The differential calculation is abstract, the block trace formula is specialized to scalar blocks, and the matrix and point-count calculations concern the specified examples. The rank-three determinant check concerns that single Gram matrix.

The manuscript supplies the constructions of the period objects and their arithmetic interpretations, together with the comparison, duality, convergence, general rank, monodromy, and Iwasawa arguments. Those arguments lie outside the present formalization. The Python computations discussed in the manuscript have their own computational record; this repository's Python wrapper records Lean execution.

## Attribution and citation

The Lean formalization, verification wrapper, and accompanying documentation were prepared with assistance from **OpenAI's ChatGPT**. The verification evidence is the successful Lean compiler run and its dependency reports, reproduced here for inspection and independent checking.

When referring to this work, cite the accompanying manuscript and identify the repository release or commit used. [`CITATION.cff`](CITATION.cff) provides basic metadata for the computational supplement.
