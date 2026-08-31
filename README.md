# LeanPlan

LeanPlan is an optimal STRIPS planner written in Lean 4.  It parses the PDDL files, grounds
the task, and runs A* over packed bit-set states.  The search, the grounder and
every heuristic carry a machine-checked proof.

The crucial idea is that an LLM agent can *write the heuristics and their
admissibility proofs*.  Writing both the heuristic and its proof in Lean turns
admissibility into a question that a kernel decides. This allows us to validate
LLM-generated heuristics mechanically instead of proving them by hand. The agent can
then propose heuristics freely, because a wrong proposal fails a check rather
than reaching a user.

Our work is inspired by previous work by [Abdulaziz, Pommerening and Corrêa
(2022)](https://abcorrea.github.io/assets/pdf/abdulaziz-et-al-icaps2022wshsdip.pdf)
and [Behnke, Kilian and Gattinger
(2026)](https://icaps26.icaps-conference.org/files/workshops/hsdip/ICAPS_HSDIP_2026_paper_11.pdf).

## The pipeline

1. **Parse and validate the PDDL.**

2. **Generate the Lean domain.**  Done automatically.

3. **Ask an agent for a heuristic.** The agent sees the Lean theory, the
   original PDDL and the heuristic interface, and returns a heuristic function
   in Lean the planner can compile.

4. **Prove admissibility.** The agent writes the proof for admissibility as well,
   one file per domain under `planner/Proofs/Domains/`, against a shared library
   that already proves grounding and search correct.  If the proof fails, the
   agent can propose a new heuristic in (3).

5. **Run the planner.**  Run A* in the tasks of the domain with the proved heuristic.

## What is proved

Every heuristic in this repository has a Lean proof that it is goal-aware and
consistent. Admissibility follows, and so does the optimality of A*.

The proof quantifies over any tasks of the domain that respect given *domain
assumptions*: statements absent from the domain file that hold across the tasks
we care about, e.g. every car in the Ferry domain has a destination goal.  These
are decidable, so the planner evaluates them before *solving a specific task*.

Grounding and search are proved once and shared, so a new domain costs one proof
file.

The proofs declare no axioms of their own (it depends only on standard
axioms), contain no `sorry`, no `admit`, no `native_decide`.

## Results

These are proof-of-concept results over the 900 test instances from the [IPC 2023
learning track](https://github.com/ipc2023-learning/benchmarks) domains. We use
300 seconds and 8 GiB for each task.  The reference planners are [Fast
Downward](https://www.fast-downward.org/) and
[Scorpion](https://github.com/jendrikseipp/scorpion).  Every plan was checked
with [VAL](https://github.com/KCL-Planning/VAL).

### Blind search

We first ran A* with a blind heuristic to evaluate the performance of the search
(e.g., successor generation, state representation, open list management). As we
can see below, LeanPlan is generally competitive but slightly worse than the two
reference planners.

| Domain      | LeanPlan | Fast Downward | Scorpion |
|-------------|---------:|--------------:|---------:|
| blocksworld |        6 |         **8** |        7 |
| childsnack  |    **9** |         **9** |    **9** |
| ferry       |        9 |        **10** |   **10** |
| floortile   |        1 |             2 |   **10** |
| miconic     |   **30** |        **30** |   **30** |
| rovers      |       12 |        **15** |   **15** |
| satellite   |   **12** |        **12** |   **12** |
| sokoban     |       24 |            26 |   **27** |
| spanner     |   **30** |        **30** |   **30** |
| transport   |    **8** |         **8** |    **8** |
| **Sum**     |      141 |           150 |  **158** |

### A* with informed heuristics

We then evaluated the same planners but now using their best available
heuristics. In our tests, LM-cut was the best heuristic for Fast Downward; for
Scorpion, we used the recommended optimal setting ("Scorpion (default)"
below). However, Scorpion hardcodes the time limits for each component
considering a 30m time limit; we ran an ablation study to identify the best time
limits for Scorpion in our benchmark with 5m time limit, and report this tuned
version as "Scorpion (tuned)".

For LeanPlan, we use the heuristic found by an agent (Claude Opus 5) using an agentic loop
similar to the one proposed by [Pereira, Corrêa, and
Seipp (2026)](https://arxiv.org/abs/2605.16142).

| Domain      | LeanPlan | Fast Down. w/ LM-cut | Scorpion (default) | Scorpion (tuned) |
|-------------|---------:|---------------------:|-------------------:|-----------------:|
| blocksworld |   **21** |                   11 |                 11 |               11 |
| childsnack  |   **14** |                    9 |                  9 |                9 |
| ferry       |   **29** |                   18 |                 19 |               19 |
| floortile   |       10 |                    9 |                 16 |           **20** |
| miconic     |       37 |                   36 |             **41** |               40 |
| rovers      |   **18** |                   17 |                 17 |               17 |
| satellite   |       23 |                   22 |                 25 |           **27** |
| sokoban     |       30 |                   29 |             **31** |           **31** |
| spanner     |   **74** |                   30 |                 30 |               30 |
| transport   |       14 |                   11 |                 13 |           **17** |
| **Sum**     |  **270** |                  192 |                212 |              221 |

## Layout

- `planner/Planner/` is the executable planner: PDDL parser and validator,
  grounding, packed states, A*, the heuristics, the generated domains and the
  registry.
- `planner/Proofs/` is the shared proof library and the ten domain proofs.
- `planner/DomainSchemaGen.lean` is the PDDL to Lean generation step.

## Building

Lean 4 and Lake, pinned by `planner/lean-toolchain`.  Install
[elan](https://github.com/leanprover/elan), then run from `planner/`:

```bash
lake build planner    # the executable
lake build Proofs     # the proofs
```

The two are separate libraries. The executable *does not* depend on the proofs,
so `lake build planner` on its own gives you a working planner.

`Proofs` is where the guarantees are checked. Lean's kernel verifies each proof
during the build. Any non-admissible heuristic will fail at this step. Since
the agent writes the proofs, this is the only step that decides whether a
heuristic is admissible.

`Proofs` depends on mathlib, pinned in `lakefile.toml` to the `v4.30.0` tag.
The first build fetches and compiles it, which takes a while.  Nothing under
`Planner/` or `Main.lean` imports mathlib, so `lake build planner` does not pay
that cost.

## Example: Adding a new domain

Below, our example assumes you want to add a heuristic `gripperHeuristic`
for the Gripper domain.  The agent writes the heuristic, its certificate and its
proof.  The build decides whether to accept them.

1. **Generate the Lean domain.**  From `planner/`:

   ```bash
   lake build domain_schema_gen
   .lake/build/bin/domain_schema_gen path/to/domain.pddl Gripper \
       Planner/GeneratedDomains/Gripper.lean
   ```
   Then add `import Planner.GeneratedDomains.Gripper` to
   `Planner/GeneratedDomains.lean`.  Generated files are never edited by hand.

2. **The heuristic**, say `gripperHeuristic` in
   `Planner/ExampleHeuristics/Gripper/GripperHeuristic.lean`.  It has type
   `Task → Heuristic`, so it reads the grounded task once and returns a `name`
   together with an `eval : State → Nat`.

3. **The certificate for domain assumptions**, alongside it.  A certificate is a
   Boolean function over the parsed domain and problem that decides the *domain
   assumptions* the proof needs. In Gripper, for example, a certificate could
   state that there are exactly two rooms in each instance. The planner runs it
   once when it loads a task and declines the heuristic if it fails, so a
   heuristic is never used on a task its proof does not cover.

4. **The registry entry**, in `Planner/ExampleHeuristics/Registry.lean`: the
   name `--heuristic` accepts, the PDDL domain name the heuristic is proved for,
   the function to build, and the certificate.  Registering is what lets the
   planner *run* the heuristic.

5. **The proof**, in `Proofs/Domains/Gripper.lean`, imported from `Proofs.lean`.
   It shows that a passing certificate gives the domain assumptions, and then
   that the compiled heuristic is goal-aware and consistent.  You must import it
   so it is checked during the build phase.

6. **Build.**  `lake build Proofs` accepts the domain or rejects it.

## Running

```bash
planner/.lake/build/bin/planner --heuristic ferry-improved domain.pddl problem.pddl
```

Note that `--heuristic blind` is always available.

Each domain has a `<domain>-simple` and a `<domain>-improved` heuristic. The
first is an admissible version of a "goal-count-like" heuristic, the second is
the heuristic obtained at the end of the CEGIS loop (similar to [Pereira,
Corrêa, and Seipp](https://arxiv.org/abs/2605.16142)).

When a task fails a domain assumption the planner names the condition and
declines the heuristic rather than searching with a guarantee that does not
apply.

Benchmarks are not tracked here.  Take them from the
[IPC 2023 learning track](https://github.com/ipc2023-learning/benchmarks).

## License

MIT.  See `LICENSE`.


## Contributors

- André Grahl Pereira
- Augusto B. Corrêa
