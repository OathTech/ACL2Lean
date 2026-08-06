# Forward design review: from ACL2Lean to broad/full ACL2 coverage

Date: 2026-08-06

## Executive conclusion

The current architecture can plausibly grow into a serious importer for a large,
useful fragment of ACL2. It cannot reach “all of ACL2” by continuing to add replay
recipes one sorting frontier at a time. Full coverage requires a shift from a
theorem-replay prototype into four coordinated systems:

1. a faithful, versioned model of the ACL2 logic and logical world;
2. a complete event/book elaborator which records the admitted logical theory;
3. an extensible proof-certificate format and verified checker for the prover's
   stable proof mechanisms;
4. a typed refinement/lifting framework for producing genuinely ACL2-free Lean
   theorems when such a translation is meaningful.

It is also necessary to define “all ACL2” precisely. ACL2 includes mechanisms which
deliberately extend trust (`defaxiom`, `skip-proofs`, trust tags, raw Lisp, trusted
clause processors), executable attachments which are not logical definitions, and
proof-search integrations whose correctness is justified externally. No sound importer
can turn all of those into unconditional Lean theorems merely by replaying an ACL2
session. The correct complete behavior is a total classification:

- **certified and replayed**;
- **certified by an independently checked certificate**;
- **conditional on explicit imported assumptions**; or
- **refused with a precise dependency explanation**.

That is achievable. “Every ACL2 theorem becomes an unconditional theorem of Lean” is
not achievable without trusting everything ACL2 itself was told to trust.

The project should therefore target **complete accountable coverage**, not universal
unconditional import: every admitted ACL2 event and every proof dependency is either
reconstructed and checked, exposed as an assumption, or rejected. The user-facing
success metric should remain narrower: unconditional, ACL2-free Lean Mirrors.

## 0.1 Is the project on track? Continue, pivot, and pause decisions

This report diagnoses the path from the present project to broad/full ACL2 coverage at
the **architecture and program level**: it identifies the missing subsystems, their
dependencies, the hard trust boundaries, a staged roadmap, and recommended allocation
of effort. It is not yet a complete implementation backlog with estimates. In
particular, the missing measured census of ACL2 community books prevents a defensible
ordering of every individual prover feature. Producing that census is itself Stage 0.

The project is **not fundamentally off-track**. Its central choices remain appropriate:

- kernel-checked proof production;
- fail-closed replay frontiers;
- instrumentation at ACL2 proof sites;
- explicit conditional obligations instead of hidden trust;
- differential testing of the semantic model; and
- progressive decoding into Lean theorems.

Work can continue in the short term. However, several prototype directions must pivot
now if “all ACL2” is a serious objective.

### Continue

The following work directly advances both the current system and the full-coverage
architecture:

- close source/log provenance and make incomplete capture fatal;
- emit explicit `include-book` edges and construct the real dependency DAG;
- complete package, reader, value, and ground-zero semantic fidelity;
- replace string conditions with typed obligations carrying exact propositions,
  world/scope identity, source events, and discharger provenance;
- establish the abstract `EvRel` and truthiness judgment layers;
- consolidate stable clausification, rewriting, substitution, and clause-composition
  fragments into verified checkers;
- complete a parametric design for `encapsulate` and functional instantiation without
  reintroducing witness bodies into certified worlds;
- develop declarative, polymorphic representation and decode kits; and
- add orthogonal benchmark families in arithmetic, abstraction/meta reasoning, stobjs,
  bit-level reasoning, and `apply$`.

Sorting should remain an important regression corpus. Work on a sorting frontier is
still worthwhile when it implements a mechanism shown to recur across ACL2—for example,
a general equivalence judgment, forcing composition, or arbitrary measure certificate.

### Pivot

1. **From sorting-driven priorities to evidence-driven breadth.** Sorting has been a
   productive architectural probe, but proximity to closing its remaining rows must no
   longer determine project priority. The community-book census and deliberately
   diverse vertical slices should select the next mechanisms.

2. **From permanent per-case walkers to progressive verified certificates.** Walkers
   remain the right discovery tool for new ACL2 proof shapes. Stable fragments should
   no longer accumulate function-, rune-, or shape-specific meta-code indefinitely;
   they should compile into reified certificates checked by proved soundness theorems.

3. **From log-only authority to independent event identity.** The production path must
   compare log-derived events/statements/worlds with a source or ACL2-expanded event
   manifest. A proof log cannot remain the sole authority for both what was proved and
   how it was proved.

4. **From names and corpus order to typed, content-addressed dependencies.** Sanitized
   declaration names, string obligation keys, and prior-corpus rule offers are prototype
   mechanisms. Full coverage needs stable event/rule/book identities and the actual
   include graph.

5. **From a broad “native” label to explicit statement tiers.** `SExpr`-level theorems
   are valuable `DecodedValue` results, and evaluator-bearing results are
   `ACL2Semantic` Mirrors. Reserve `NativeLean` for statements with no ACL2 value,
   evaluator, world, or term vocabulary unless the ACL2 datatype is intentionally the
   theorem's subject.

6. **From instrumented stdout to a supported proof artifact.** Structured text has
   enabled rapid progress, but the destination is a versioned, checksummed artifact
   with explicit completion, source/include/world identity, and trust-taint records,
   ideally maintained or upstreamed with ACL2.

### Pause or tightly constrain

Until the corresponding foundations land, avoid:

- bespoke handling of another isolated sorting rewrite/window shape;
- new theorem-, builtin-, recognizer-, or measure-name registries where emitted data or
  a generic certificate can express the same fact;
- Lean-side closure inferred from the absence of an ACL2 event;
- expansion of the decision-procedure carve-out before leaf origins and premise
  identity have a formal policy;
- reporting conditional, assumed, `SExpr`-only, or evaluator-bearing results as
  completed native imports;
- onboarding more books through corpus-order dependency over-offering; and
- hand-written native bridges whose theorem-to-replay pairing is protected only by the
  present reachability seam gate.

This is therefore a **directed pivot, not a rewrite or moratorium**. Preserve the proven
core, continue safe foundational work, use walkers for discovery, and require new
features to fit the future world/certificate/native-lifting architecture.

### Recommended next milestone

Before another large book-family closeout, demonstrate all of the following together:

1. content-addressed source, include-closure, expanded-event, world, and proof-artifact
   identities;
2. fatal/atomic capture with an explicit successful completion record;
3. typed cross-book and conditional dependencies over the real include DAG;
4. at least one stable replay fragment handled by a verified certificate checker; and
5. one unconditional, ACL2-free `NativeLean` theorem from each of two non-sorting
   domains.

That milestone would show that ACL2Lean has moved from a strong sorting-centered
prototype onto a credible path toward broad ACL2 coverage without discarding its
existing accomplishments.

## 1. Define the coverage contract first

The repository currently uses CORE / EXTENDED / OUT tiers. For full-ACL2 planning,
replace that with an explicit matrix along three independent axes.

### Logical admission status

- `KernelReplayed`: Lean checks a replay/certificate from definitions and prior facts.
- `KernelDerived`: Lean checks a permitted decision procedure on the exact obligation.
- `AssumptionBacked`: the result has named hypotheses for `defaxiom`, trusted processor,
  warrant, unknown constraint, or other external knowledge.
- `Rejected`: the logical dependency cannot be represented faithfully.

### Statement level

- `ACL2Semantic`: evaluator/world proposition.
- `DecodedValue`: pure proposition over the ACL2 value datatype, with no evaluator.
- `NativeLean`: theorem over ordinary Lean types and operations, with no ACL2 notions.

### Fidelity level

- `EventAuthentic`: source, expanded event, log, world, and statement identities match.
- `ProofAuthentic`: every logical transition is tied to an ACL2 record or a declared
  certificate class.
- `ReasoningFaithful`: the accepted proof follows ACL2's selected proof route rather
  than merely proving the same leaf independently.

Without this matrix, “coverage” will keep mixing parse coverage, conditional replay,
decision-procedure closure, and genuine native imports.

## 2. Major missing foundation: the complete ACL2 logical universe

### 2.1 Values and reader/package semantics

ACL2's logical universe includes conses, symbols with package identity, strings,
characters, rationals, complex rationals, and canonical numeric equality. Current open
bugs already identify missing complex rationals, incomplete package imports and package
markers, escaped symbol syntax, reader macros, and package-sensitive builtin dispatch.

Full coverage needs:

- a unique canonical representation of every ACL2 object;
- the exact package/import table and `defpkg` evolution;
- ACL2/Common Lisp tokenization and readtable-case behavior;
- complex-rational arithmetic, equality, ordering/completion behavior, and printing;
- faithful symbol interning/home-package identity;
- a versioned primitive manifest for every ground-zero function used by books;
- rejection before admission whenever a value lies outside the implemented universe.

This is not merely interpreter polish. Every quoted constant, rune, substitution,
theory expression, package-qualified function, and Mirror encoding depends on it.

### 2.2 Complete term semantics

The small logical term core—variables, quote, `if`, lambdas, and applications—is
manageable, but ACL2 surface forms expand through macros and world-dependent aliases.
The importer needs a canonical translated-term artifact emitted after ACL2 translation,
not an independent approximation of surface macro expansion.

Important extensions include:

- `mbe`, `ec-call`, `prog2$`, `return-last`, `wormhole`, and other logical/executable
  split forms;
- multiple values (`mv`, `mv-let`) after translation;
- constrained and choice functions;
- `apply$`, badges, warrants, tame functions, and quoted/lambda function objects;
- state and stobj signatures in logical terms;
- package-aware macro aliases and generated functions.

The design should treat ACL2's translated term as authoritative and compare it with any
source-side translation used for provenance. Reimplementing all ACL2 macro expansion in
Lean would be high-cost and unnecessary.

### 2.3 Ground-zero world and ACL2 versioning

The current cited-closure snapshot strategy is appropriate for a bounded fragment, but
full coverage needs a principled base-world package:

- exact ACL2 version/commit;
- complete logical definitions, constraints, primitive axioms, rule classes,
  congruences, tau rules, type prescriptions, linear rules, well-founded relations, and
  executable counterparts relevant to that version;
- a proof or generated validation that the Lean base semantics agrees with ACL2;
- content-addressed snapshots rather than name-based registries.

A theorem's identity must include the base-world identity. “ACL2 theorem X” is not
stable across arbitrary ACL2 versions, books, packages, and theory state.

## 3. Major missing subsystem: event and world completeness

The production Mirror path currently consumes log-derived `Development` events, while
the source generator explicitly refuses many ACL2 events. Full book coverage requires
modeling the logical effect—not necessarily the UI behavior—of at least these families.

### 3.1 Definitions and admissions

- `defun`, `defund`, `mutual-recursion`, `verify-termination`, custom measures, multiple
  measured variables, ruler extenders, well-founded relations, and program-to-logic
  transitions;
- `defchoose` and `defun-sk`, including choice/Skolem axioms and functional
  instantiation behavior;
- `defexec`, logic/exec body separation, and guard dependencies;
- `defstobj` and `defabsstobj` logical definitions, recognizers, accessors, updaters,
  creator functions, correspondence and preservation theorems;
- `defconst`, generated definitions, macro-generated events, and `make-event` expansion.

The important principle is to import the **expanded logical event sequence ACL2
actually admitted**. Supporting every user macro syntactically is unnecessary if ACL2
emits a canonical expansion with source provenance.

### 3.2 Theorems and rule installation

`defthm` is only the beginning. The world must preserve:

- every rule class and its corollary: rewrite, definition, type-prescription, linear,
  forward-chaining, elimination, generalization, induction, congruence, equivalence,
  refinement, meta, clause-processor, tau-system, and built-in-clause rules;
- `defequiv`, `defrefinement`, `defcong`, `defevaluator`, and generated rule events;
- enabled/disabled theories, named theories, `in-theory`, `set-body`, and theorem
  visibility at each proof point;
- match-free settings, backchain limits, case-split settings, default hints, computed
  hints, override hints, and world tables which change proof interpretation;
- `local` scope, nested `encapsulate`, redundancy, undo/redefinition behavior where it
  affects admitted books.

The importer need not reproduce heuristic search settings to check a complete
certificate, but it must record enough state to authenticate why a cited rune or
processor was legal at that event.

### 3.3 Books, packages, and dynamic event generation

Full ecosystem coverage depends more on book elaboration than on another sorting
lemma:

- canonical `include-book` graph with `:dir`, certification identity, portcullis,
  local events, and transitive dependencies;
- package definitions/imports and package changes;
- `make-event` and macro expansion recorded as admitted expanded events;
- theory/table state and event-generated events;
- certificate provenance and ACL2 version compatibility;
- duplicate names across packages/books and redundant event handling.

Build a content-addressed **World Manifest** whose nodes are expanded logical events and
whose edges are exact dependencies. This should replace corpus-order offers and string
lookups.

## 4. Major missing subsystem: complete proof-mechanism coverage

### 4.1 Rewriter completeness

The rewriter is ACL2's center of gravity. Full coverage requires a general checker for:

- arbitrary generated equivalence relations (`geneqv`), refinement lattices, patterned
  equivalences, and user congruence rules;
- conditional rewrite rules, free-variable matching, backchaining, relieved hypotheses,
  ancestors/loop prevention, forced hypotheses, and hide/double-rewrite behavior;
- meta rules, metafunction contexts, hypothesis metafunctions, syntaxp/bind-free,
  equivalence-preserving metafunction results, and evaluator constraints;
- rewrite-quoted-constant rules and large quoted structures;
- executable counterparts, congruence-based argument rewriting, lambda application,
  and conditional branch assumptions;
- exact enabled-theory and rule-class provenance.

Per-feature meta-code will become unmaintainable here. The existing hybrid plan should
be accelerated: stabilize an open `EvRel` judgment, then build a reified rewrite
certificate and prove its checker sound once. New relation/rule kinds should extend
certificate data and local soundness modules, not add theorem-specific walkers.

### 4.2 Full waterfall and cross-goal structure

The following need first-class proof objects and composition semantics:

- preprocessing, clausification, simplification, settled-down transitions;
- destructor elimination, fertilization, generalization, irrelevance elimination;
- subsumption, case splitting, induction pool management, merged and mutual induction;
- forcing rounds and the exact discharge of forced assumptions;
- `:use`, `:by`, `:cases`, `:or`, `:induct`, computed hints, and constraint clauses;
- guard and termination proof waterfalls;
- proof-builder output if proof-builder-authored theorems are to count as faithfully
  replayed rather than merely re-proved.

The current proof tree is a useful discovery representation. For full coverage it must
become a versioned certificate schema with explicit begin/end/completeness records and
no semantic inference from missing events.

### 4.3 Induction and recursive admission generality

Sorting exercises useful list recursions but not the full admission engine. Needed:

- arbitrary measures into arbitrary admitted well-founded relations;
- lexicographic/ordinal measures and the full ACL2 ordinal domain;
- several measured arguments, controller combinations, ruler extenders;
- clique/mutual recursion and flagged induction;
- merged induction schemes and induction suggested by rules rather than definitions;
- partial/conditional termination workflows and later `verify-termination`;
- stobj-recursive and `apply$`-related admissions.

This should be certificate-driven: emit the admitted measure theorem and well-founded
relation dependency exactly, replay those proofs, then use a generic Lean well-founded
recursion theorem. Avoid registries keyed by familiar measure-function names.

### 4.4 Decision procedures

ACL2 uses type-set reasoning, tau, linear and nonlinear arithmetic, polynomial
normalization, built-in-clause procedures, congruence closure-like reasoning, and
specialized libraries such as GL/BDD/SAT integrations.

There are three honest strategies per procedure:

1. emit and check a proof certificate;
2. reconstruct the exact proposition and use a trusted/verified Lean decision procedure;
3. expose a named assumption or refuse.

“ACL2 returned proved” is never enough. The current DP carve-out should become a plugin
interface whose contract includes origin, exact clause, premises, semantics, checker,
and axiom policy. Arithmetic needs rationals and nonlinear certificates, not only
`omega`. Bit-level ecosystems need bit-blasting/SAT certificates. GL's symbolic
execution needs either verified translation or independently checkable AIG/CNF proofs.

## 5. Hard boundary: meta rules and clause processors

ACL2 permits user code to transform terms and clauses. Trusted clause processors can
be admitted under trust tags; verified clause processors and meta rules rely on
correctness theorems expressed through evaluator functions.

This is a major architectural frontier, not another rune recipe.

For **verified** meta rules/processors:

- import/replay their correctness theorem first;
- represent the evaluator and metafunction/processor as logical ACL2 functions;
- record the actual input, output, substitution/context, and correctness rune;
- instantiate the correctness theorem in Lean to certify the transformation;
- handle state/global-context access and meta-extract hypotheses explicitly.

For **trusted** processors, raw Lisp, or trust tags:

- never label the result unconditional;
- introduce a precise assumption describing the processor's semantic preservation, or
  refuse according to policy;
- propagate that dependency transitively into every affected theorem and native Mirror.

This dependency tainting must occur at the world/event level, not as an ad hoc replay
hypothesis discovered only when the processor fires.

## 6. Hard boundary: axioms, constrained functions, and functional instantiation

Complete ACL2 includes justified conservative extensions and unjustified assumptions.
They must not share one mechanism.

### Conservative mechanisms

- `encapsulate` with local witnesses;
- `defchoose`/`defun-sk` choice principles;
- functional instantiation;
- abstract stobjs and correspondence theorems.

These require parametric worlds/models, constraint satisfaction, witness/conservativity
proofs, scope identity, and exact functional substitutions. The current witness
exclusion fix is only the first safety condition. The final theorem must quantify over
all implementations satisfying constraints, never use a captured local witness body.

### Non-conservative/trusted mechanisms

- `defaxiom`;
- `skip-proofs` and uncertified inclusions;
- trust tags and raw-mode events;
- trusted clause processors or externally asserted facts.

These must produce explicit Lean axioms/hypotheses in a quarantined namespace, with a
machine-readable taint graph. Native catalog policy should default to rejecting tainted
theorems; an opt-in conditional export may expose the assumptions.

## 7. Execution features: stobjs, guards, attachments, and raw Lisp

ACL2's logic/execution duality must be handled carefully.

- Ordinary single-threaded objects are logically lists/records; their logical theorems
  can be imported without modeling destructive execution. However, event generation,
  guards, recognizers, accessors/updaters, and abstract-stobj correspondence still need
  faithful world support.
- Guards are usually not part of logical theorem truth, but guard verification produces
  proof obligations and controls executable counterparts. Full event coverage must
  replay or classify those obligations and keep logical and executable bodies distinct.
- `mbe` and `defexec` require the logical body for theorem semantics and a separate
  correspondence story if executable behavior is mirrored.
- `defattach` must not redefine logical meaning. Attachments may affect evaluation used
  during proof search; any proof step depending on an attachment needs a certificate or
  explicit trust dependency.
- Raw Lisp and stateful side effects are outside the pure ACL2 logic. Support should mean
  faithfully classifying their logical consequences, not simulating arbitrary Common
  Lisp inside Lean.

## 8. `apply$` and higher-order ACL2

The current evaluator is first-order. Modern ACL2 books can use `apply$`, function
objects, badges, tame functions, warrants, `defun$`, and scions. This affects logic,
admission, rewriting, and constraints.

A full design needs:

- a representation of ACL2 function objects/lambdas;
- logical `apply$` semantics over the supported function universe;
- badge and tameness predicates;
- warrants as explicit theorem dependencies;
- simulation/lifting rules for higher-order native Lean functions;
- package/world identity for function symbols and generated warrant functions.

This is a substantial new evaluator layer. It should be isolated behind a function-
application interface now, before more first-order code directly pattern-matches on
application heads.

## 9. Native Mirrors at full scale

Automatic proof replay and automatic native theorem production are different problems.
There is no canonical Lean-idiomatic reading for every ACL2 theorem. ACL2 functions are
untyped, total via completion rules, and often mix domains. A sound native bridge needs
a refinement specification.

Build a first-class representation framework containing:

- a Lean type, encoding, partial decoder, and recognizer theorem;
- proof that encoding is injective/canonical;
- per-function logical-domain preconditions and a simulation theorem;
- predicate/relationship interpretations;
- completion-rule handling outside the represented domain;
- composition and polymorphism for lists, alists, records, numbers, bitvectors, trees,
  finite maps, ordinals, and stobjs;
- theorem-level translation with explicit narrowing and side conditions.

The terminal artifact should be generated from a declarative mapping, not a long hand
proof. When no mapping exists, stop at `ACL2Semantic` or `DecodedValue`; do not weaken
the definition of Native Mirror. A theorem over `SExpr` can be a useful decoded theorem,
but it is not automatically ACL2-free.

## 10. Proof artifact and checker architecture

The current meta-walker approach is excellent for discovering real ACL2 proof shapes.
At full scale it will suffer from code growth, proof-term size, elaboration time, and
duplicated validation logic. The repository's hybrid proposal is correct but should be
made a central program now.

Recommended shape:

- a versioned, self-describing certificate envelope with source/world/prover hashes;
- fragment-local certificate types for rewriting, clausification, induction,
  substitutions, DP leaves, and waterfall composition;
- executable Lean checkers with proved soundness into open judgments (`EvValue`,
  `EvRel`, `EvTrue`, clause truth, world extension);
- no monolithic closed derivation datatype;
- walkers retained as diagnostic compilers from ACL2 emission into certificates;
- content-addressed sharing of terms, substitutions, rules, and subproofs;
- streaming parsing/checking for very large books;
- deterministic error locations back to book/event/clause/rewrite step.

This is necessary for thousands of community books. Re-elaborating enormous bespoke
proof expressions per theorem is unlikely to scale.

## 11. Instrumentation strategy

The fork currently instruments selected prover sites. Full coverage requires the proof
artifact to be a supported ACL2 interface, ideally upstreamed.

Priorities:

1. explicit capture completion/failure and source/include manifests;
2. event expansion and logical-world delta emission;
3. complete ttree/provenance payloads at processor boundaries;
4. forcing-round and hint obligation edges;
5. rule installation and enabled-theory snapshots/deltas;
6. meta/clause-processor invocation certificates;
7. trust-tag, axiom, attachment, and skip-proofs taint events;
8. stable schema versioning and compatibility tests against new ACL2 releases.

Long term, parsing human-oriented stdout is the wrong boundary. ACL2 should write a
machine artifact through a dedicated channel with length framing/checksums and a schema
version. The instrumented fork must be continuously rebased or upstreamed; otherwise
“all ACL2” will mean one increasingly old private ACL2 version.

## 12. Where effort should go beyond sorting

### Priority A — breadth measurement before more feature implementation

Run a machine census over the ACL2 community books and representative industrial books.
Measure, per admitted theorem and per firing step:

- event kinds and translated term features;
- rule classes actually installed and fired;
- waterfall processors and hint kinds;
- induction/measure/well-founded-relation shapes;
- forcing, meta, clause-processor, tau/linear/nonlinear/GL usage;
- `encapsulate`, functional instantiation, `defun-sk`, stobj, and `apply$` prevalence;
- trust tags, axioms, skip-proofs, and uncertified dependencies;
- package/reader/value features;
- potential native datatypes and theorem shapes.

The 2026-06 survey explicitly says its measured sweep never happened. This is now the
highest-leverage planning task. Feature frequency should decide the next architecture
work, not proximity to the sorting frontier.

### Priority B — choose deliberately diverse benchmark families

Keep sorting as a regression corpus, but add vertical slices selected to attack
orthogonal architecture:

1. **Arithmetic:** rational and nonlinear arithmetic, floor/mod, expt, inequalities.
2. **Bitvectors/hardware:** logops, bit blasting, GL/SAT certificate boundary.
3. **Records/alists:** packages, generated macros, fixtypes, congruence/refinement.
4. **Quantified/abstract:** `encapsulate`, `defchoose`, `defun-sk`, functional
   instantiation.
5. **Meta reasoning:** a small verified metafunction and a verified clause processor.
6. **Stateful models:** concrete and abstract stobj books, logical-only import first.
7. **Higher order:** a minimal `apply$`/warrant book.
8. **Proof builder/hints:** computed hints, forcing rounds, `:by`, and custom induction.

For each family, require one end-to-end ACL2-free native theorem—not merely a green
semantic replay row—so the Mirror architecture evolves with replay breadth.

### Priority C — authenticity and world infrastructure

Before adding many books, implement the source/log/world manifest, include DAG, expanded
event stream, package model, and typed dependency IDs identified in the first audit.
Every later feature becomes safer and easier once it plugs into a correct world graph.

### Priority D — consolidate the stable proof core

Move clausification, rewrite chains, substitution, and clause composition into verified
checkers. Sorting has supplied enough examples to stabilize these fragments. Continuing
to grow only meta-walkers will accumulate prohibitive maintenance debt.

### Priority E — constraints and external knowledge

Complete parametric `encapsulate`, functional instantiation, choice/Skolem events, and
cross-book theorem replay. These are central to serious ACL2 developments and to a sound
world model. Simultaneously build the taint graph for non-conservative assumptions.

### Priority F — industrialize native lifting

Develop declarative, polymorphic refinement kits alongside each new benchmark family.
The project should measure `NativeLean` results, not just replayed rows. Otherwise broad
ACL2 coverage can produce a large catalog which still exposes ACL2 semantics to Lean
users.

## 13. Proposed staged roadmap

### Stage 0 — scope and metrics

- Ratify complete accountable coverage as the meaning of “all ACL2.”
- Adopt the three-axis status matrix.
- Complete the ecosystem mechanism census.
- Select the diverse benchmark suite and pin current outcomes.

### Stage 1 — artifact/world integrity

- Content-address source, includes, base world, expanded events, and proof log.
- Emit explicit successful completion and trust/axiom taints.
- Implement package/reader/value completeness for the selected ACL2 version.
- Replace corpus-order/name registries with typed world/event/rule IDs.

### Stage 2 — stable proof kernel

- General `EvRel`/truth judgments.
- Verified certificate checkers for clausify, rewriting, substitution, and tree
  composition.
- Full forcing/hint/structural-waterfall certificates.
- Generic induction/admission certificates over arbitrary well-founded relations.

### Stage 3 — logical event breadth

- Full rule classes and theory state.
- Parametric encapsulate and functional instantiation.
- `defchoose`, `defun-sk`, guards/verify-termination, concrete stobj logical events.
- Meta rule and verified clause-processor certificate path.
- Explicit assumption/refusal path for trusted extensions.

### Stage 4 — specialized reasoning ecosystems

- Rational/nonlinear arithmetic certificates.
- Bitvector/SAT/GL proof-certificate integrations.
- Abstract stobjs.
- `apply$`, badges, warrants, and higher-order lifting.

### Stage 5 — native import industrialization

- Declarative representations and simulations for major Lean datatypes.
- Generated theorem decoders with narrowing/side-condition checks.
- Public ACL2-free modules separated from semantic/replay internals.
- Per-book reports showing unconditional `NativeLean` coverage and taint status.

### Stage 6 — maintenance and release

- Upstream or formally maintain the ACL2 artifact interface.
- Version-compatibility matrix across supported ACL2 releases.
- Incremental/content-addressed checking at community-book scale.
- Fuzz source/event/value/proof artifacts and differential-test generated programs.
- Publish a reproducible theorem manifest containing every dependency and digest.

## 14. Concrete next twelve-month focus recommendation

If resources are limited, do not spend the next cycle finishing every sorting row.
Allocate effort approximately as follows:

- **25% artifact and world integrity:** source/include/event manifests, packages, typed
  identities, taint tracking.
- **20% measured breadth and diverse corpora:** census plus arithmetic, abstract,
  meta, stobj, and higher-order slices.
- **25% verified replay-core consolidation:** rewrite/clausify/tree certificate checkers.
- **15% constraints and cross-book logic:** encapsulate, functional instantiation,
  choice/Skolem support.
- **15% native lifting industrialization:** polymorphic representations and generated
  ACL2-free Mirrors.

Sorting should consume only the effort needed to keep it as a regression and to finish
features which the broader census confirms are common. Its remaining bespoke path,
measure, or rewrite-window cases should not automatically outrank package correctness,
event completeness, meta reasoning, or a true native lifting framework.

## Final assessment

ACL2Lean's current foundations—kernel checking, fail-closed frontiers, emitted proof
structure, conditional obligations, and differential semantics—are the right ones.
The project is not architecturally trapped in sorting. The main danger is incremental
success creating the illusion that ACL2 completeness is a long list of similar replay
cases. It is not.

The decisive work is to make the logical world and artifact identities complete, turn
stable replay fragments into verified certificate checkers, classify trust extensions
honestly, and build native refinements as a first-class product. With those changes,
covering the ACL2 logical ecosystem is a credible long-term research program. Without
them, adding more books will increase the number of kernel-checked propositions while
leaving the hardest authenticity, scalability, and user-facing Mirror problems intact.
