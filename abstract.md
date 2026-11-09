[Read the annotated paper](paper.html) for a short introduction with the formal definitions, results, and proofs alongside the text.

We give three representations of finite temporal graphs on a fixed vertex set: (1) a sequence of snapshots, (2) a footprint with finite time labels, and (3) a chronological list of temporal edge occurrences. Equal-time edge occurrences have no prescribed order.

We define strict and nonstrict temporal walks, paths, reachability and temporal graph settings. Removing a closed segment turns a walk into a shorter walk with the same endpoints. On proper graphs, the departure times of every nonstrict path are already strictly increasing. Examples distinguish paths from walks, simplicity from properness, and illustrate why opposite arcs may share a timestamp.

An occurrence may have a natural traversal time. Waiting is allowed, the lifetime bounds departure times, and the final arrival may follow the last snapshot. Uniform traversal times one and zero recover strict and nonstrict paths respectively, with the same vertices and departure times, and therefore the same reachability.

We define five interpretations of optimal temporal paths for a fixed source, target, release time and arrival deadline: shortest, fastest, foremost, latest-departure and minimum-waiting paths. Each objective admits an optimal path whenever the query is feasible. With uniform traversal time c, elapsed time is total internal waiting plus c times the number of hops. Three-vertex examples separate all five optimality predicates for strict temporal paths (uniform traversal time one). For nonstrict paths (uniform traversal time zero), fastest and minimum waiting coincide.
## Guide to the concepts

- [Three representations of temporal graphs](Lax330177.Representations.html) defines snapshots, time-labelled footprints and chronological event lists, and proves how to convert between them.
- [Temporal graph settings](Lax330177.Settings.html) defines directed and undirected settings, strict and nonstrict modes, and simple, proper and happy labellings.
- [Paths, walks and reachability](Lax330177.Paths.html) defines timed walks, paths and reachability. It proves that deleting cycles preserves reachability and that strict and nonstrict paths coincide on proper graphs.
- [Traversal times](Lax330177.Durations.html) allows each edge occurrence its own traversal time and proves that uniform times zero and one recover nonstrict and strict paths, respectively.
- [Counterexamples](Lax330177.Examples.html) separates simplicity from properness, shows why the proper-path theorem fails for walks, and gives a happy undirected graph with asymmetric, nontransitive reachability.
- [Optimal temporal paths](Lax330177.OptimalPaths.html) defines shortest, fastest, foremost, latest-departure and minimum-waiting paths and proves that each optimum is attained whenever a feasible path exists.
- [Optimality under uniform traversal times](Lax330177.UniformCosts.html) expresses elapsed time in terms of hops and waiting and proves what fastest paths minimize at traversal times zero and one.
- [Three-vertex examples separating path objectives](Lax330177.CostExamples.html) compares routes on a chain and on a triangle to show which optimality criteria can select different paths.
- [The temporal reachability graph](Lax330177.ReachabilityGraph.html) records reachable pairs of distinct vertices as arcs of a static digraph.
