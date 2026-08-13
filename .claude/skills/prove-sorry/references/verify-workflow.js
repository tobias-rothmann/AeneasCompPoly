// TEMPLATE — adversarial verification of a just-integrated proof (and statement
// change, if one was made). Adapt placeholders, write to the scratchpad, launch
// with Workflow({scriptPath}). Four independent audit lenses -> completeness
// critic. Same DSL contract and no-backticks rule as prove-workflow.js (see its
// header). Auditors are read-only on the repo and must back every claim with
// file:line, a compiled snippet, or a concrete counterexample.
// If NO statement change was made: repurpose the 'hypothesis' lens per its
// prompt's final paragraph instead of deleting it.

export const meta = {
  name: 'verify-proof',
  description: 'Adversarially verify the new proof: faithfulness, hypothesis minimality, empirical cross-check, integrity',
  phases: [
    { title: 'Audit', detail: 'four independent adversarial lenses' },
    { title: 'Critic', detail: 'completeness critic over the audit findings' },
  ],
}

const PROJ = '<ABSOLUTE-PROJECT-ROOT>'
const SCRATCH = '<ABSOLUTE-SCRATCHPAD-DIR>'

const COMMON = [
'You are adversarially auditing a just-completed Lean 4 verification. FIND PROBLEMS;',
'do not confirm good work. If you find nothing after genuine effort, say so plainly.',
'',
'## Context',
'<WHAT WAS PROVED, WHAT STATEMENT CHANGE WAS MADE AND ITS STATED RATIONALE>',
'',
'## Files',
'- <FILE UNDER AUDIT + the list of newly added declarations>',
'- <GROUND-TRUTH MODEL / SOURCE CODE>',
'- <REFERENCE LIBRARY>',
'- <SCRATCHPAD DISPROOF FILE, if a hypothesis was added>',
'',
'## Ground rules',
'- Verify with: cd ' + PROJ + ' && lake env lean <file> — and ONLY that. Do NOT run',
'  lake build: it takes the Lake lock and other auditors run concurrently. (The one',
'  exception is spelled out in the integrity lens.)',
'- Scratch files go under ' + SCRATCH + '/audit-<lens>-*.lean.',
'- READ-ONLY on all repo/library sources. Report problems; do not fix them.',
'- Back every claim with evidence; label unsubstantiated hunches as such.',
].join('\n')

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['lens', 'verdict', 'findings', 'checksPerformed', 'notes'],
  properties: {
    lens: { type: 'string' },
    verdict: { type: 'string', enum: ['clean', 'concerns', 'broken'] },
    findings: {
      type: 'array',
      items: {
        type: 'object',
        additionalProperties: false,
        required: ['severity', 'claim', 'evidence'],
        properties: {
          severity: { type: 'string', enum: ['critical', 'major', 'minor', 'nit'] },
          claim: { type: 'string' },
          evidence: { type: 'string' },
        },
      },
    },
    checksPerformed: { type: 'array', items: { type: 'string' } },
    notes: { type: 'string' },
  },
}

const LENSES = [
  {
    key: 'faithful',
    prompt: [
'## YOUR LENS: faithfulness & vacuity of the statements',
'1. Does the main spec assert what a reader wants — including that the program',
'   SUCCEEDS (check the triple/spec definition is not vacuously satisfied by',
'   failure or divergence)?',
'2. Is the reference operation the right one (trimmed vs raw, canonical forms)?',
'3. Is the abstraction function right, the equality non-trivial?',
'4. Read each auxiliary lemma: is it a faithful description of its code?',
'5. VACUITY: for each lemma, exhibit a compiled concrete instance where ALL',
'   hypotheses hold, so the lemma provably has content.',
    ].join('\n'),
  },
  {
    key: 'hypothesis',
    prompt: [
'## YOUR LENS: the added/changed hypothesis',
'1. NECESSITY: independently re-verify the machine-checked disproof of the',
'   original statement (compiles, clean axioms, refutes the REAL old statement,',
'   not a strawman).',
'2. MINIMALITY: is it the weakest natural form? Off-by-ones matter (intermediate',
'   computations can fail before the final one). Try to PROVE a stronger theorem',
'   from a weaker hypothesis in scratch; report if you succeed.',
'3. SUFFICIENCY: enumerate EVERY fail/div point in the code path (checked',
'   arithmetic, pushes, indexing) and confirm the hypotheses rule each out,',
'   including exact boundary cases.',
'4. Does the change break any downstream caller?',
'If NO statement change was made, do 3 and 4 for the ORIGINAL hypotheses and',
'additionally audit statement strength: could the theorem be stated more strongly,',
'or an existing hypothesis be weakened? Skip 1-2 (there is no disproof file).',
    ].join('\n'),
  },
  {
    key: 'empirical',
    prompt: [
'## YOUR LENS: empirical cross-check on concrete inputs',
'Independently of the proof, test the SPECIFICATION: in scratch files, #eval BOTH',
'sides on concrete inputs and compare — the extracted function (a Result; expect',
'ok, and treat any fail as a finding in itself) against the reference',
'implementation mapped through the representation function. Cover:',
'empty/degenerate inputs; small generic cases; <THIS DOMAIN\'S EDGE BEHAVIORS —',
'e.g. values near the modulus exercising wraparound, inputs where',
'canonicalization/trimming actually fires>. native_decide is BANNED; plain',
'#eval + decide are fine. Report any disagreement as critical, and list exactly',
'which cases you evaluated and which you could not, so coverage is visible.',
    ].join('\n'),
  },
  {
    key: 'integrity',
    prompt: [
'## YOUR LENS: proof integrity & composition',
'You are the ONE lens permitted to run lake build (once, if needed to confirm the',
'full build): run it late in your audit to minimise Lake-lock contention with the',
'other auditors, and retry once if it fails on a lock.',
'1. Full build passes; zero sorries in the file; #print axioms on EVERY theorem',
'   in the file shows only [propext, Classical.choice, Quot.sound] (dependencies',
'   may contain sorries — sorryAx would surface here).',
'2. Hidden escapes: native_decide, @[implemented_by], unsafe, axiom, maxHeartbeats,',
'   shadowing declarations.',
'3. COMPOSITION: check every seam where one lemma feeds another — do the',
'   instantiations line up, are invariant seeds actually established by the',
'   producer, could a scalar_tac/omega discharge be succeeding for a wrong reason?',
'   If a precondition was added: can the spec compose with ITSELF (chain it in a',
'   scratch file) — does the postcondition expose enough to discharge the',
'   precondition of the next application?',
'4. Loop proofs: measures genuinely decrease; invariants non-vacuous.',
'5. New attributes (@[simp] etc.): safe, load-bearing, or gratuitous?',
    ].join('\n'),
  },
]

phase('Audit')
log('running ' + LENSES.length + ' adversarial audit lenses')

const audits = (await parallel(LENSES.map(function (l) {
  return function () {
    return agent(COMMON + '\n\n' + l.prompt + '\n\nReturn the structured result. Set lens="' + l.key + '".',
      { label: 'audit:' + l.key, phase: 'Audit', schema: SCHEMA, model: 'opus', effort: 'xhigh' })
  }
}))).filter(Boolean)

phase('Critic')
const digest = audits.map(function (a) {
  return '### lens ' + a.lens + ' — verdict ' + a.verdict +
    '\nchecks: ' + (a.checksPerformed || []).join('; ') +
    '\nfindings:\n' + (a.findings || []).map(function (f) {
      return '  [' + f.severity + '] ' + f.claim + '\n     evidence: ' + f.evidence
    }).join('\n') + '\nnotes: ' + a.notes
}).join('\n\n')

const critic = await agent(
  COMMON + '\n\n## YOUR LENS: completeness critic\n' + [
'Four auditors have reported (below). 1. Identify what NOBODY checked. 2. Adjudicate',
'disagreements by going to the source. 3. Independently spot-verify the 2-3 most',
'load-bearing claims — especially any claim that everything is fine. 4. Do the',
'missing checks yourself with the compiler. Report only findings that SURVIVE your',
'verification; say which auditor findings you dropped and why.',
'',
'## Auditor reports',
'',
  ].join('\n') + digest + '\n\nReturn the structured result. Set lens="critic".',
  { label: 'critic', phase: 'Critic', schema: SCHEMA, model: 'opus', effort: 'max' }
)

const all = critic ? audits.concat([critic]) : audits
function sev(s) { return all.flatMap(function (a) { return (a.findings || []).filter(function (f) { return f.severity === s }) }) }
log('critical=' + sev('critical').length + ' major=' + sev('major').length + ' minor=' + sev('minor').length)

return {
  verdicts: all.map(function (a) { return { lens: a.lens, verdict: a.verdict } }),
  // the critic's findings are the adjudicated list; raw lens findings may
  // include claims the critic refuted — read criticNotes before acting
  criticFindings: critic ? critic.findings : null,
  criticNotes: critic ? critic.notes : null,
  critical: sev('critical'),
  major: sev('major'),
  minor: sev('minor'),
  nits: sev('nit'),
  checksPerformed: all.map(function (a) { return { lens: a.lens, checks: a.checksPerformed } }),
}
