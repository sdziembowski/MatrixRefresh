# Matrix refreshing and circuit compilation in Lean

This Lean/mathlib 4.35.0 project accompanies *Leakage-Resilient Computation via
Matrix Refreshing*. It formalizes
continual refreshing, the direct NAND compiler, signed composition with causal
history-dependent labels, and stateful oracle simulation. Only the constructions
and proof dependencies used by the current manuscript are retained.

The standalone [Annotated Lean Reference Specifications](annotated-specifications.pdf)
note explains the current public definitions and theorem statements with generated
code listings.

## Folder guide

| File or folder | Contents |
| --- | --- |
| `Refreshing.lean`, `Proofs/Refreshing/` | Continual-refreshing model, bundled reference theorem, and independent proofs. |
| `Compiler.lean` | Direct and stateful source circuits, compilation programs, physical execution, local and adaptive interfaces, and bundled compiler theorem. |
| `EfficientSimulation.lean` | Counted execution, simulators, and bundled simulation theorem. |
| `annotated-specifications.pdf` | Standalone annotated reference note. |
| `scripts/` | Proof-layout checker. |
| `Proofs/ReferenceClaims.lean` | Imports the three public reference modules for the comparator challenge. |
| `Proofs/Compiler/Direct/` | Correctness, resource counts, physical refresh chains, and privacy of the NAND compiler. |
| `Proofs/Compiler/Adaptive/`, `Proofs/Compiler/Stateful/` | Online public inputs, chronological unrolling, public interaction, and continual privacy. |
| `Proofs/Compiler/DirectComposition/` | Energy trimming, incidence-three Hölder, signed tensor discrepancy, joint expansion, causal normalization, and marked-set summation. |
| `Proofs/Compiler/Construction/`, `Proofs/Compiler/GateApproximation/` | Correctness and distribution identities for the sampling algorithms, and their local analytic certificates. |
| `Proofs/Compiler/Operations/` | Correctness, locality, and exact physical-distribution proofs for computation, refresh, and public-sampling instructions. |
| `Proofs/EfficientSimulaiton/` | Exact simulator marginals, accounting identities, and expected-work proofs. |
| `Proofs/Compiler/Foundations/`, `Proofs/Compiler/LocalComparisons/` | Probability, linear algebra, scoped networks, and local estimates used by the current proofs. |

The root contains exactly three Lean source files: `Refreshing.lean`,
`Compiler.lean`, and `EfficientSimulation.lean`. Each contains its model
definitions, admitted construction certificates where needed, and one admitted
main theorem. `Refreshing.lean` imports only
Mathlib; `Compiler.lean` may additionally import `Refreshing`; and
`EfficientSimulation.lean` may import both earlier modules. Definitions are
placed in the earliest public file that needs them. `Refreshing.main_theorem`
states its components directly. Compiler and EfficientSimulation expose named
`Prop` declarations for their components, with numerical bounds in those
propositions, and each main theorem bundles them. Together these cover the
eight previously separate results. Their proofs are
named after the corresponding results:
`Theorem41.lean`, `Theorem52.lean`, `Theorem57.lean`, and `Theorem61.lean`.
The compiler contains source and program definitions, physical execution,
local estimates, adaptive interfaces, and the remaining sampler definitions.
Counted execution and simulator definitions are in `EfficientSimulation.lean`;
correctness arguments are under `Proofs/`.
`comparator.json` lists the bundled theorem and construction-certificate
targets by declaration name.

Substantive proofs and proof-only definitions belong under `Proofs/Refreshing/`,
`Proofs/Compiler/`, or `Proofs/EfficientSimulaiton/`. Elementary arithmetic and
finite-index proofs may appear inline in public definitions. Public files contain no
proof-only theorem statements. They expose the model definitions and admit
needed construction certificates with `by sorry`; each has exactly one admitted
main theorem and imports no `Proofs` module. For example, the compiler's
`rawRetryDistribution` remains explicit while its acceptance certificate is
proved in `Proofs/Compiler/PublicModel.lean`. The comparator checks the
certificate against that proof. The main theorem proofs are assembled from the
topic folders.

`Proofs/ProvedClaims.lean` builds the proof development. `Proofs/ReferenceClaims.lean`
imports the three isolated public reference modules.
The `Operations` namespace in `Compiler.lean` describes the physical
instruction engine shared by the direct and stateful compilers. Its counted
execution is in `EfficientSimulation.lean`.
Proof modules use independent data copies that omit the admitted public main
theorems and supply complete construction certificates. `Proofs/Compiler/Model.lean` and
`Proofs/EfficientSimulaiton/Model.lean` add the proof-only normalization and
execution helpers. The comparator checks the bundled reference statements
against that independent proof environment.

## Correspondence with the paper

The table uses the manuscript's stable LaTeX labels, since theorem numbers may
change during editing. Paths below are relative to this directory.

| Paper statement or proof step | Lean files | Mathematical correspondence |
| --- | --- | --- |
| Leakage model and Theorem 4.1 (`thm:main`) | `Refreshing.lean`, `Proofs/Refreshing/Model.lean`, `Proofs/Refreshing/Theorem41.lean` | The same nonzero binary shares, matrix refresh, adaptive deterministic strategies, and complete transcript distance. The bundled refreshing statement includes encoding nonemptiness and the security bound. |
| Spectral truncation and local refresh approximation (`lem:copy-local`) | `Proofs/Refreshing/LocalSVD.lean`, `LocalNuclear.lean`, `GramVariance.lean`, `ConsistencySign.lean`, `FourCycleTransfer.lean` | Actual Gram matrices and singular directions, the strict cutoff, nuclear/factor bounds, consistency-sign cancellation, and the fourth-moment error estimate. |
| Refreshing hybrids (`sec:copy-comparison`) | `Proofs/Refreshing/Hybrids.lean`, `ReplacementCosts.lean`, `WindowCosts.lean`, `LocalToGlobal.lean` | One signed transition moves along the label boundary. True endpoint distributions and local replacement costs give the `T K³ q^(-1/9)` bound. |
| Protected NAND, refreshing, and shortening (`lem:compiler-local-interface`) | `Compiler.lean`, `Proofs/Compiler/GateApproximation/Interfaces/Gadget/Interface.lean`, `Proofs/Compiler/Operations/ComputeCertificate.lean`, `RefreshCertificate.lean` | Tensor inputs, refresh the long encoding, and shorten it. Local certificates include full rejected proposal tapes and all retries. |
| Physical refresh chains (`sec:compiler-direct`) | `Compiler.lean`, `Proofs/Compiler/Direct/Correctness.lean`, `Incidence.lean`, `Resources.lean` | Refresh both NAND ports, including repeated operands. Prove `S=3g+U`, distinct physical operands, scope size three, and incidence three. |
| Trimming (`clm:direct-trimming`) | `Proofs/Compiler/DirectComposition/Trimming.lean` | Separate left/right energy masks at `B=q^(1/9)` turn the valid-label `L₂` error into an `L₃` error. |
| Hölder and tensor discrepancy (`clm:direct-product-holder`, `clm:direct-encoding-discrepancy`) | `Proofs/Compiler/DirectComposition/Holder.lean`, `TensorDiscrepancy.lean`, `EncodingDifference.lean`, `ProductFactors.lean` | Incidence-three Hölder and tensorized signed weights `D_b=μ_b−ν`, with original encoding distributions on error scopes. |
| Joint marked expansion and resummation (`sec:direct-marked-expansion`) | `Proofs/Compiler/DirectComposition/Expansion.lean`, `ExecutionExpansion.lean`, `MarkedTensor.lean`, `FiniteMarks.lean`, `InclusionExclusion.lean` | Expand local errors and changing-wire differences together. Sum signed marked-wire weights before taking absolute values, then resum true factors. |
| History-dependent labels and normalization (`thm:direct-composition`) | `Compiler.lean`, `Proofs/Compiler/Adaptive/Model.lean`, `Proofs/Compiler/DirectComposition/HistoryLabels.lean`, `AdaptiveTheorem57.lean` | Sample a wire after choosing its label from earlier answers. Sum unguarded answers together with outside encoding weights. Never freeze future encodings while summing earlier answers. |
| Stateless compiler and simulator (`thm:compiler-direct`, `sec:direct-simulator`) | `Proofs/Compiler/Direct/Theorem52.lean`, `Proofs/EfficientSimulaiton/Direct/Runtime.lean`, `Parameters.lean`, `Theorem52.lean` | Actual local certificates and canonical execution imply privacy. The zero-input simulator has an exact physical marginal and a polynomial expected-work bound. The parameter proof uses `18λ−n/27` directly. |
| Stateful compiler and online simulation (`thm:compiler-stateful`) | `Proofs/Compiler/Stateful/Interaction.lean`, `Timing.lean`, `Unrolling.lean`, `Decoder.lean`, `Theorem61.lean`, `Proofs/EfficientSimulaiton/Stateful/` | Chronological input sampling, retained state, authorized output releases, a common causal public observation, and the same signed-composition bound over all invocations. |

The fixed-label and causal composition propositions are defined in
`Compiler.lean` and bundled in `Compiler.main_theorem`; their model interfaces are in
`Compiler.lean`. The fixed-label proof is in
`Proofs/Compiler/DirectComposition/Theorem57.lean` and is used by the stateless
compiler. The causal interface generalizes the labels for stateful use and
reuses the same trimming, tensor, expansion, and summation arguments.

The formal proofs choose explicit conservative constants. Local certificates
allow separate mean energies of eight instead of the paper's four. They use
an arbitrary-label `L₂` allowance of twelve and explicit discrepancy constants.
These allowances are carried through the proof and absorbed into the `10⁶`
prefactor. The construction, probability normalization, leakage exponents, and
incidence assumptions are unchanged. No global privacy or marked-sum bound is
assumed by a local certificate.

## Models and quantitative guarantees

A wire stores `(L,R)` in `(𝔽₂ⁿ \ {0})²` and encodes `L·R`. Initial private
encodings are trusted. Public inputs and constants are sampled under leakage.
Only the active operation's local shares, messages, and sampling records enter
its callbacks. Both parties' functions in a phase are selected before either
current answer is known. Shortening may depend on the preceding matrix-phase
answer. Communication is private, and the refresh matrix is erased before
shortening. Output shares are hidden and the trusted decoder reveals plaintext.

The NAND source allows arbitrary fanout, repeated operands, zero gates, unused
inputs, directly designated input outputs, and repeated output positions.
AND/OR/NOT conversion is mathematical preprocessing outside this checked source
interface. Strategies are deterministic. The paper's external averaging over
adversary tapes is not part of the checked headline statements. The protocol's
own randomness, rejected proposals, and retries are part of the model and proofs.

Writing `λ=matrixLeakage+shorteningLeakage`, `K=2^(2λ)`, and `q=2^n−1`:

```text
refreshing distance ≤ 12000 T K³ q^(-1/9)
compiler distance ≤ 1000000 S K⁹ q^(-1/27)
                  ≤ 2000000 S 2^(18λ−n/27).
```

The stateful theorem also caps the distance by one. The compiler's sufficient
share length is `n ≥ 12000(κ+λ+ln(S+2))`, with `κ ≥ 1` and `n ≥ 2`.
The logarithm is natural. This follows directly from the current binary bound,
without a selector compiler, multiple approximation tiers, or a weaker rate.

The formal cost model deliberately counts random sampling, scalar arithmetic
and tests, and explicitly charged preparation operations, including the
corresponding costs of every rejected proposal and shortening retry. Routine
memory-access and address bookkeeping is left to the conventional implementation
analysis. This keeps the formal development focused on the probabilistic and
cryptographic arguments.

For a stateless source with `P` private inputs, `U` public/constant inputs,
`g` NAND gates, and `k` output positions, Lean proves the following bound on the
expected value of this counter:

```text
trusted encodings = P
S = 3g+U
local-answer evaluations = 8g+2U
expected counter ≤ P+k+16P(6n+1)+100S(n²+2)³.
```

For `T` invocations of a transition circuit with `m` register bits, `d` public
input bits, `c` constants, `g` NAND gates, and `k` output positions, the same cost
convention gives:

```text
trusted encodings = m, initialized once
S = 3Tg+Td+c
local-answer evaluations = 8Tg+2(Td+c)
expected counter ≤ m+Tk+16m(6n+1)+100S(n²+2)³.
```

Stateful constants are sampled once. Each invocation's public input is chosen
from earlier leakage and earlier public input/output records, then sampled at
that invocation's start. The retained register addresses implement the source
transition. Its plaintext outputs are released at the invocation's end.
State/output positions may alias. Zero-invocation and zero-operation executions
are permitted, which strengthens the paper's positive-horizon statement.

The stateful simulator is one oracle-parametric function, quantified before the
private initial state. It initializes zero registers and executes the actual
physical operations. At each invocation's end it queries the ideal oracle with
that invocation's input and publishes its authorized response, without revealing
the dummy output values or encodings. Encodings needed for the next state or
later uses remain available internally. An encoding may be erased once its last
required use has finished. The oracle interface is a mathematical function
of the chronological request history and current request. Recursive public
records describe a cache of earlier authorized responses. Timing and input-prefix
lemmas justify their causal availability. The real decoder is proved equal to
these authorized outputs, so the full view is the same deterministic function
of each experiment's leakage transcript.

Ideal-oracle evaluation and adversary computations, including input choice,
public-history processing, and leakage functions, are charged separately. A uniform charge `R`
per local-answer evaluation adds the displayed callback count times `R`. Joint
accounting can instead add tape-dependent extra work without independence.
These are probability and counter bounds, not certification of extracted
interactive code. The capped simulator, within-phase adaptive extension, and
larger-field extension remain outside the checked statements.

## Build and audit

Clone this repository and enter the Lean project:

```sh
git clone https://github.com/sdziembowski/MatrixRefresh.git
cd MatrixRefresh/version-1.0/lean
```

From this directory:

```sh
lake exe cache get       # first setup, if dependencies are not cached
lake build
lake comparator --paranoid
```

From this directory, check the proof-folder boundary with:

```sh
python3 scripts/check_lean_proof_layout.py
```

`comparator.json` lists the main theorem targets covering the eight formalized
results, plus the admitted construction certificates as definition targets. Each
public main theorem and certificate deliberately contains `sorry`. Complete
proofs are loaded in a separate environment and
do not import those admitted declarations.
The auditor compares statements, underlying
definitions, proof dependencies, and proof terms. Only `propext`, `Quot.sound`,
and `Classical.choice` are permitted axioms. Human review must still establish
that a formal statement expresses the intended mathematical claim.

We recommend the comparator's sandbox. If it is unavailable, the explicitly
unsandboxed fallback is:

```sh
lake comparator --paranoid --inadvisably-no-sandbox
```

This disables OS isolation while retaining the statement and proof checks.
Project configuration and executed code receive the invoking user's permissions.
**Use the fallback at your own risk, only for code you trust.**

`.lake/packages/` contains downloaded dependencies and their build cache.
`.lake/build/` contains generated products of this project. They are not extra
formalizations. Obsolete local products can be removed when their source module
is deleted. The working dependency cache is retained to avoid downloading and
rebuilding mathlib for each audit.

## Proof folding

Mathematical comments describe the definitions and proofs, with one comment
paragraph per source line. Proofs use ordinary indentation folding.
VS Code supports **Fold All** with **⌘K, ⌘0** on macOS
or **Ctrl+K, Ctrl+0** elsewhere. **Unfold All** uses **⌘K, ⌘J** or
**Ctrl+K, Ctrl+J**. These are successive key chords.
