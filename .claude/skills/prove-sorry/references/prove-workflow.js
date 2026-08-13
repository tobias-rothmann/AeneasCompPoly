// TEMPLATE — adapt, then write to the scratchpad and launch with Workflow({scriptPath}).
// Replace every <ANGLE-BRACKET> placeholder; rewrite TASKS and the DETAIL_* blocks
// for the concrete decomposition. Shape: N parallel prover attempts per lemma,
// first compiling attempt wins, failures escalate to one repair agent.
//
// Workflow DSL this script relies on (provided by the Workflow tool runtime):
//   agent(prompt, {label, phase, schema, model, effort}) -> Promise<object|null>
//     (with schema: returns the validated object; null if the agent dies/is
//      skipped — hence the .filter(Boolean) and the 'repair agent died' branch)
//   parallel([...thunks]) -> Promise<results[]>   barrier; failed thunks -> null
//   pipeline(items, ...stages) -> per-item chaining, no cross-item barrier;
//     every stage receives (prevResult, originalItem, index)
//   phase(title), log(msg) -> progress display only
// If the Workflow tool is absent, run the same prompts as parallel Agent-tool
// calls with identical schemas — the orchestration below is just
// attempts -> first-compiling-wins -> repair.
//
// RULES OF THE ROAD:
// - NO template literals / backticks anywhere: Lean snippets contain backticks and
//   break the Workflow script parser. Build all prompt text from '\n'-joined arrays.
// - Prover agents run model 'opus' at effort 'xhigh'; repair agents at 'max'.
// - The scaffold file must ALREADY typecheck (with sorry bodies) before launching.
// - lake build must have been run once beforehand; agents only use lake env lean.

export const meta = {
  name: 'prove-sublemmas',
  description: 'Prove the decomposed sub-lemmas of the target theorem in parallel',
  phases: [
    { title: 'Prove', detail: 'parallel attempts per lemma, self-verified with lake env lean' },
    { title: 'Repair', detail: 'escalate any lemma where no attempt compiled' },
  ],
}

const PROJ = '<ABSOLUTE-PROJECT-ROOT>'
const SCRATCH = '<ABSOLUTE-SCRATCHPAD-DIR>'

const PREAMBLE = [
'You are proving one Lean 4 theorem. Be rigorous and persistent: iterate until it compiles.',
'',
'## Environment',
'- Project root (cwd for all lean commands): ' + PROJ,
'- Toolchain / deps: <TOOLCHAIN; PATHS TO THE AENEAS LEAN BACKEND, THE REFERENCE LIBRARY,',
'  AND THE EXTRACTED MODEL>',
'- A SHARED SCAFFOLD file already typechecks: ' + SCRATCH + '/scaffold.lean',
'  It imports the built library, proves shared helpers, and states all target',
'  lemmas with sorry bodies.',
'',
'## HARD RULES',
'- NEVER modify repo source files, anything under .lake, or the scaffold itself.',
'- NEVER run "lake build". Verify with:  cd ' + PROJ + ' && lake env lean <your-work-file>',
'  (concurrency-safe; roughly <PROBE-TIME>s per run).',
'- Do NOT change the STATEMENT of any theorem. If you become convinced your target',
'  is FALSE as stated, stop and report a concrete counterexample instead.',
'- FORBIDDEN: sorry, native_decide, new axioms, @[implemented_by], unsafe.',
'  set_option maxHeartbeats is acceptable if genuinely needed — say so in notes.',
'- You MAY add private helper lemmas ABOVE your theorem; name them <lemma>_aux and report them.',
'',
'## Workflow',
'1. cp ' + SCRATCH + '/scaffold.lean <YOUR_WORK_FILE>',
'2. Replace ONLY your lemma sorry. Leave the other sorry bodies alone — you MAY',
'   use the other sorried statements as if proved.',
'3. Verify. SUCCESS = zero "error:" lines AND the "declaration uses sorry" warning',
'   at YOUR lemma is gone (warnings for the other lemmas are expected).',
'4. Write ONLY your helpers + finished theorem (pasteable, no imports/opens) to <YOUR_OUT_FILE>.',
'5. Re-verify once more before finishing.',
'',
'## Reference material — READ FIRST',
'- <FILE WITH NEIGHBOR PROOFS TO IMITATE — name the specific proofs>',
'- <GENERATED/MODEL CODE UNDER VERIFICATION, with line ranges>',
'- <LIBRARY FILES: spec combinators, datatype specs>',
'',
'## Key facts already established (compiler-verified — do not re-derive)',
'- <PASTE THE PHASE-0 PROBED API FACTS: exact lemma names, statements, step behavior>',
'- <PASTE THE GOTCHAS FROM THE SKILL APPENDIX THAT APPLY HERE>',
].join('\n')

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['lemma', 'compiles', 'outFile', 'workFile', 'helperNames', 'notes'],
  properties: {
    lemma: { type: 'string' },
    compiles: { type: 'boolean', description: 'true only if verification passed as defined above' },
    outFile: { type: 'string' },
    workFile: { type: 'string' },
    helperNames: { type: 'array', items: { type: 'string' } },
    notes: { type: 'string', description: 'what you did, surprises, any set_option; if compiles=false the exact remaining goal + errors' },
  },
}

// One entry per sub-lemma. detail = full statement (verbatim from the scaffold),
// why it is true, a suggested proof skeleton, and the tricky sub-steps.
// attempts: 1 for routine pieces, 2 for the hard ones.
const TASKS = [
  { key: 'A', attempts: 1, label: '<short label>', detail: ['<DETAIL LINES>'].join('\n') },
  // ...
]

function proverPrompt(t, n) {
  const wf = SCRATCH + '/work-' + t.key + '-' + n + '.lean'
  const of = SCRATCH + '/out-' + t.key + '-' + n + '.lean'
  const variation = n === 1
    ? '\nNOTE: another agent attempts this lemma independently following the skeleton. Consider a DIFFERENT decomposition first (e.g. extract the pure reasoning into a standalone helper proved separately from the plumbing). Diversity is the point.'
    : '\nNOTE: another agent is attempting this lemma independently via a different route. Follow the suggested skeleton closely; prioritise compiling.'
  return PREAMBLE + '\n\n## YOUR ASSIGNMENT: lemma ' + t.key + ' — ' + t.label +
    '\nYOUR_WORK_FILE = ' + wf + '\nYOUR_OUT_FILE  = ' + of + '\n\n' + t.detail +
    (t.attempts > 1 ? variation : '') +
    '\n\nReturn the structured result. compiles=true ONLY per the success criterion; else put the exact remaining goal in notes.'
}

function repairPrompt(t, attempts) {
  const wf = SCRATCH + '/repair-' + t.key + '.lean'
  const of = SCRATCH + '/out-' + t.key + '-repair.lean'
  const reports = attempts.map(function (a, n) {
    return '--- attempt ' + n + ' (workFile ' + a.workFile + ') ---\nnotes: ' + a.notes
  }).join('\n')
  return PREAMBLE + '\n\n## REPAIR lemma ' + t.key + ' — ' + t.label +
    '\nAll previous attempts failed. READ their work files first (salvage partial progress).\n\n' +
    reports +
    '\n\nYOUR_WORK_FILE = ' + wf + '\nYOUR_OUT_FILE  = ' + of + '\n\n' + t.detail +
    '\n\nBe maximally persistent: alternative tactics (omega, scalar_tac, simp_lists, grind, aesop,' +
    '\nexact?), inspect goals with trace_state, split hard steps into standalone helpers.' +
    '\nDo NOT change the statement.' +
    '\n\nReturn the structured result.'
}

phase('Prove')
log('proving ' + TASKS.length + ' lemmas (' + TASKS.reduce(function (a, t) { return a + t.attempts }, 0) + ' attempts)')

const results = await pipeline(
  TASKS,
  // stages receive (prevResult, originalItem, index); bind the item from the
  // second parameter so the shape is correct regardless of how the runtime
  // seeds the first stage's prevResult
  function (_first, t) {
    return parallel(Array.from({ length: t.attempts }, function (_, n) {
      return function () {
        return agent(proverPrompt(t, n), {
          label: 'prove:' + t.key + (t.attempts > 1 ? '#' + n : ''),
          phase: 'Prove', schema: SCHEMA, model: 'opus', effort: 'xhigh',
        })
      }
    })).then(function (rs) { return rs.filter(Boolean) })
  },
  function (attempts, t) {
    const ok = attempts.find(function (a) { return a.compiles })
    if (ok) { log(t.key + ': compiled'); return Object.assign({ task: t.key, repaired: false }, ok) }
    log(t.key + ': no attempt compiled — escalating to repair')
    return agent(repairPrompt(t, attempts), {
      label: 'repair:' + t.key, phase: 'Repair', schema: SCHEMA, model: 'opus', effort: 'max',
    }).then(function (r) {
      return r ? Object.assign({ task: t.key, repaired: true }, r)
        : { task: t.key, repaired: true, compiles: false, notes: 'repair agent died', outFile: '', workFile: '', helperNames: [] }
    })
  }
)

const final = results.filter(Boolean)
log('done: ' + final.filter(function (r) { return r.compiles }).length + '/' + TASKS.length + ' compiling')
return { summary: final }
