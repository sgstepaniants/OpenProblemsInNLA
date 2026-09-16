# SF-01: independent review of two observed foundation repairs

**Approve these exact two proof-body repairs for a Linux rerun.** This is a
narrow continuation of my first-foundation mathematical review. It does not
approve the eight later analytical/converse modules, claim a complete SF-01
proof, or report successful compilation of the replacements.

Reviewer `/root/mi04_independent_referee` is a nonauthor of the SF-01 files;
the repair author is `/root/ie13_continuation`. The author manifest is
`b4bdf08644b4854f9175c69ac3beabadea26ef081e14a4b8ee8d2ebf2fec0dc8`.
The integrity-bound 17-file candidate closure is
`aab365c85c8afbd291212358548bc06bca1a130a8b6ce2c9a1d279e5f7414ee7`.
I read both complete changed modules, the full patch, all 33 lines of the
actual module log, all 24 Challenge log lines, the author's evidence records,
the prior foundation review and the exact relevant pinned API definitions.

`complexify_isUnit_iff` retains the original determinant-based proof of unit
reflection for every dimension. The actual goal is precisely the equivalence
between nonzero complex coercion of a real determinant and nonzero real
determinant. `Complex.ofReal_ne_zero` is that equivalence in the inspected
pinned source. Replacing the unused equality lemma with this nonzero lemma
changes no hypothesis or conclusion, including the empty-dimensional case.
It does not assume a spectral condition, invertibility or positive weight.

`half_coefficient_positive` still multiplies the existing exact LeanCert
half certificate by a positive real coefficient. The actual simplified
expression retains `1 * 2⁻¹`. Adding the ordinary `one_mul` rule removes that
factor and gives the unchanged `a / 2` conclusion. The certificate itself,
explicit kernel setting, and consumption in `initial_data_valid` are unchanged.
No numerical interval, precision parameter or mathematical premise is added.

The independent audit passed 209 checks and rehashed all 19 packet entries
and 102 external author bindings. `SOURCE-PATHS.json` was followed explicitly:
only the two packet `after/` files replace their stale author-workspace
versions. The other fifteen candidate files are byte-identical. All 92
existing headers, all 24 original Challenge contracts, nine frozen inputs,
pins, imports, options and trust commands remain unchanged. The two relevant
Mathlib files were independently checked against their literal pinned Git
objects. No proof hole, custom axiom, native shortcut, resource change or
contact address was introduced.

Actual run `35090376438` executed literal commit
`0ce7dc10d8b901ee57e8d226f36a30979bb205aa`, on Linux as UID 1001. I compared
all nine first-foundation sources and the full Challenge directly with Git
and the actual receipt; all eleven post-command maps equal its 1,929-input
initial map. Both SF-01 logs match their ZIP members and unique ordered raw
GitHub job-log windows. The two changed files actually failed, while the
unchanged IV03 files and WeightedZReuse built. The certificate and initial-data
axiom prints show the ordinary foundational axioms, but the failed Numerical
module is not a clean successful prefix build. The 24 specification holes
elaborated separately; no Comparator ran.

The eight later modules are absent from this run. Their hashes and preserved
headers are reconciled here only to prevent an unnoticed concurrent change;
their mathematical approval requires their separate reviews. The original
full Newton target, Colbrook mathematical attribution, George Stepaniants'
Caltech department/university credit, Sidney Holden's unchanged IV03 reuse,
AI disclosure and licenses remain under the prior foundation review.

No Lean, Lake, cache or Comparator was executed locally. I changed no author
source, shared worktree, Git state, publication or count. Actual rerun,
completion and final whole-proof reviews, and canonical kernel/Comparator/
control/publication evidence remain required.
