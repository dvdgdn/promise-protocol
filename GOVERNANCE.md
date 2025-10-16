# Promise Protocol Governance : How the Protocol is Extended 
**Platform Cooperative · Executable Specifications · Open Participation**

Promise Protocol is a **platform cooperative (eG)** that runs on **executable specs**. Anyone can contribute—workers, coaches, reviewers, users, or external collaborators—so long as your work **passes the specs**. We keep **decentralized innovation** aligned through a small set of **core protocol boundaries**.

This document explains **how to contribute**, what **kinds of contributions** exist, and how we recognize them through **Patronage** (surplus sharing) and **Merit** (governance weight). It complements, but does not replace, the project’s overarching **CONTRIBUTING.md (Proof-of-Contribution & Compensation)**.

---

## Core Principle: Protocol, Not Gatekeepers
Promise operates like an **open protocol**:
- **Core Protocol Specs** define non-negotiables (payments posture, outcome validity, data integrity, consumer protection).
- **Domain Standards** define quality rules in specific areas (e.g., sleep coaching metrics, evidence templates).
- **Experiments** let you launch new templates or tools **permissionlessly**, provided they **satisfy Core**.

You don’t need permission to build—you need to **pass the specs**.

---

## Three Ways to Contribute

### 1) Use the Protocol (Patronage)
Deliver value via existing specs:
- **Coaches (Providers):** Run programs that achieve **KEPT** outcomes → earn patronage via net GMV kept.
- **Reviewers/Certifiers:** Produce verified **ABDUCTIO** exports → earn patronage by usage in official dossiers.
- **Workers/Contributors:** Build/operate the platform → earn patronage via wages/hours.
- **Users/Clients (who are members):** May earn a small patronage share via spend/engagement.

**Specs to read:** `protocol/core/*.feature`, `domains/*/standards/*.feature`

---

### 2) Improve the Protocol (Merit)
Create or enhance specs **others adopt**:
- Publish a coaching template (Gherkin) → earn **Merit** when independent coaches use it.
- Design an evidence template → earn **Merit** when reviewers adopt it.
- Build a tool with tests → earn **Merit** proportional to usage.
- Propose a Core enhancement → gains **Merit** if merged.

> **Merit = governance weight in its domain** (not money; does not override reserved matters).

**Process:** See **Merit System** below.

---

### 3) Expand the Ecosystem (Experiments)
Build permissionless innovations that remain **outside Standards** until they prove out:
- New promise types that satisfy `protocol/core/promise_validity.feature`
- New methods that hit outcome criteria
- Integrations that pass `protocol/core/interop.feature`
- Tools that improve UX while honoring Core

**If it passes Core, you can deploy it.**  
**Specs:** `protocol/core/*.feature`

---

## How Contributions Are Recognized

### A) Patronage (Economic Distribution)
Classic cooperative surplus sharing based on **usage** (final weights decided by the GA per Satzung):

| Stakeholder Class      | Measure                                   | Typical Allocation* |
|------------------------|--------------------------------------------|---------------------|
| Providers (Coaches)    | Net GMV from **KEPT** outcomes             | ~50% of patronage   |
| Reviewers/Certifiers   | Verified ABDUCTIO exports in dossiers      | ~20%                |
| Workers/Contributors   | Wage share **or** hours                    | ~25%                |
| Users/Clients (members)| Spend/engagement                           | ~5%                 |

\* Final percentages are defined in the **Surplus Policy** and may change by GA vote.

**Triggered by:** Year-end surplus allocation (Satzung §11)  
**Verified by:** `finance/surplus_allocation.feature`

---

### B) Merit (Governance Influence)
**Merit Points = Adoptions × Quality Score × Time Decay**

- **Adoptions:** Count of **independent** adoptions (see “Independence” below).
- **Quality Score:** Outcome metrics (KEPT rates, export acceptance, uptime, etc.).
- **Time Decay:** Recent contributions weigh more (default half-life 6 months).

**Merit grants:**
- Increased **weight** in **domain** governance (e.g., sleep standards).
- Priority for **spec bounties**.
- Public **leaderboard** recognition.

**Merit does NOT grant:**
- ❌ Extra votes on **reserved matters** (one-member-one-vote remains).
- ❌ Direct money (use patronage or posted bounties).
- ❌ Control over Core without GA approval.

**Defined by:** `governance/merit_calculation.feature`

**Independence rule:** An “independent adoption” means **distinct organizations / billing entities with no common control**. Self-use does not count toward adoption thresholds.

---

## Governance Layers

### Layer 1 — Core Protocol (**Reserved Matters**)
**Changes require:** Concurrent majorities (majority of all members **and** a simple majority within each stakeholder class), plus any GenG super-majorities where applicable.

**Controlled by:** `protocol/core/*.feature`
- `payment_flows.feature` — No custody, refund rules, consumer rights
- `promise_validity.feature` — ABDUCTIO/SPONSIO outcome criteria semantics
- `data_integrity.feature` — Provenance, privacy, portability, “no black-box decisions”
- `governance_rules.feature` — Multi-stakeholder voting, investing member limits

**Who can change:** Only GA per Satzung §8.

---

### Layer 2 — Domain Standards (**Class-Majority**)
**Changes require:** Majority within the relevant stakeholder class.

**Organized by domain:**
- `domains/sleep/standards/*.feature` — Providers vote on sleep coaching criteria
- `domains/evidence/standards/*.feature` — Reviewers vote on evidence templates
- `domains/platform/standards/*.feature` — Workers vote on tooling/UX standards

**Who can change:** The **relevant class** via proposal + vote. Standards must remain compatible with Core.

---

### Layer 3 — Experiments (**Permissionless**)
**Requirements:** Must pass Core specs; otherwise unconstrained.

**Location:** `experiments/*/` (templates, method variants, prototypes)

**Who can deploy:** Anyone who demonstrates Core compliance.

---

## Merit System (Detailed)

### Earning Merit
1. **Create a Spec**
   - Write a Gherkin spec in `domains/{area}/proposals/`.
   - Include rationale, examples, validation thresholds.
   - Submit PR with tests and reference implementation.

2. **Get Adoption**
   - Used by **≥ 3 independent** actors (see independence rule).
   - Verified via transaction logs (KEPT outcomes, exports, tool usage).
   - Active for **≥ 30 days**.

3. **Maintain Quality**
   - Track outcome metrics continuously.
   - Merit accrues per usage × quality multiplier.
   - Regressions reduce Merit.

4. **Earn Compounding Merit**
   - If your spec becomes a **Standard**, derivatives credit your attribution chain.
   - Attribution is tracked in `governance/merit_attribution.feature`.

### Time Decay (defaults; centralized in one config)
```
current_merit = base_merit × 0.5 ^ (months_since_contribution / 6)
```
(Keep the decay constants in a single source of truth referenced by all docs.)

### Applying Merit
- **Domain Vote Weight:**
```
vote_weight = 1.0 + log10( your_domain_merit / median_domain_merit )
```
Capped at **3.0×** per vote.

- **Spec Bounty Priority:** Higher-Merit contributors in the relevant domain are notified first.

- **Transparency:** Quarterly Merit reports; challenges allowed via issue + evidence review.

---

## Contribution Workflows

### For Coaches (Providers)
**Goal:** Launch a new sleep program spec.

1. Read: `protocol/core/promise_validity.feature`
2. Choose or author a template:
 - Use: `domains/sleep/standards/isi_delta_v1.feature`
 - Propose: `domains/sleep/proposals/{your_method}.feature`
3. Implement program to pass the spec.
4. Run tests locally: `npm test domains/sleep/...`
5. Register your promise; enroll clients.
6. Earn: patronage (GMV kept) and, if adopted by others, **Merit**.

**Refs:** `domains/sleep/standards/isi_delta_v1.feature`

---

### For Reviewers/Certifiers
**Goal:** Issue Tragfähigkeit evidence with ABDUCTIO.

1. Read: `protocol/core/abductio_export.feature`
2. Use or enhance:
 - Use: `domains/evidence/standards/tragfaehigkeit_v1.feature`
 - Enhance: PR improvements
3. Generate exports with deterministic JSON/PDF.
4. Hash/provenance verification must pass.
5. Submit; validations enforce `abductio_export.feature`.
6. Earn: patronage by export usage; Merit if others adopt your improvements.

**Refs:** `protocol/core/abductio_export.feature`, `domains/evidence/standards/tragfaehigkeit_v1.feature`

---

### For Workers/Contributors
**Goal:** Build a new dashboard feature.

1. Read: `protocol/core/interop.feature`, `domains/platform/standards/dataviz.feature`
2. Write the spec first:
 - `domains/platform/proposals/revenue_dashboard.feature`
 - Include reproducibility, a11y, performance
3. Implement with tests.
4. Document usage + integration.
5. Deploy after CI passes.
6. Earn: patronage via wages; Merit from broad stakeholder usage.

**Refs:** `domains/platform/standards/dataviz.feature`

---

### For Users/Clients
**Goal:** Propose a new outcome metric.

1. Research which metrics help evaluate coaches.
2. Draft spec: `domains/sleep/proposals/user_satisfaction_v1.feature`
3. Seek feedback in community forum.
4. Submit PR with rationale and examples.
5. Vote (if a member of the relevant class).
6. Earn: Merit if adopted and used by independent providers.

---

## Technical Requirements

**All Contributions Must:**
- ✅ Pass **Core** (`protocol/core/*.feature`)
- ✅ Include test coverage (≥ 80% for new code)
- ✅ Produce **deterministic outputs** (same inputs → same results)
- ✅ Document **provenance** (sources, methods, hashes)
- ✅ Respect privacy/consumer rights (GDPR, 14-day withdrawal, etc.)

**Contributions Should:**
- Use namespaced files: `{domain}/{type}/{name}_v{version}.feature`
- Tag appropriately: `@reserved_matter`, `@domain_standard`, `@experiment`
- Include example tables with realistic data
- Link to policy rationale (“why this spec exists”)
- Specify governance scope (who can modify it)

---

## Spec Lifecycle
**Proposal → Review → Adoption → Active → Maintenance → Sunset**

- **Proposal:** Anyone submits to `domains/{area}/proposals/` with rationale, tests, and reference impl.
- **Review:** Community feedback; CI runs; relevant class reviews.
- **Adoption:** ≥ 3 independent users within 90 days **or** class vote to fast-track → move to `.../standards/`.
- **Active:** In production; Merit accrues; monitored for quality.
- **Maintenance:** Usage < 10 events/month for 3 months → maintenance mode (slower Merit).
- **Sunset:** No usage for 6 months & not compliance-critical → archived (revivable if needed).

---

## Bounty System (Specs & Tools)
The GA or Board posts **spec bounties** funded from the Product & Risk Fund.

**Example Bounty**
- **Title:** AVGS Coaching Evidence Template  
- **Domain:** evidence  
- **Budget:** €2,000  
- **Criteria:**  
- Passes `protocol/core/abductio_export.feature`  
- Accepted by ≥ 2 AZAV-certified providers  
- Validated by Prüfungsverband within 30 days  
- **Deadline:** 2026-03-31  
- **Priority:** High-Merit reviewers notified first

**Claiming:**  
1) Comment on the bounty issue with your proposal → 2) Submit PR → 3) Demonstrate adoption/criteria → 4) Receive payment + Merit upon acceptance.

---

## Anti-Gaming Safeguards

### Merit Integrity
- ❌ **Fake usage:** Merit only from **verified** transactions/ledgers.
- ❌ **Self-dealing:** Your own usage does **not** count toward adoption thresholds.
- ❌ **Spec spam:** No adoption within 90 days → archived.
- ❌ **Quality slippage:** Poor outcomes reduce Merit.

### Governance Protection
- ❌ **Merit ≠ override:** Reserved matters remain **one-member-one-vote**.
- ❌ **Merit caps:** Max 3× weight in domain governance.
- ⏳ **Time decay:** Keeps influence current.
- ⚖️ **Class balance:** Concurrent majorities preserve minority classes on Core.

### Transparency & Audit
- ✅ Public merit math in `governance/merit_calculation.feature`
- ✅ Spec usage logged and auditable
- ✅ Quarterly Merit reports
- ✅ Anyone may challenge scores; evidence-based review by GA/Board

---

## Getting Started

1. **Choose your path**
 - Use Protocol → `protocol/core/*.feature`
 - Improve Protocol → `domains/*/standards/*.feature`
 - Experiment → `experiments/*/`

2. **Set up dev**
 - `git clone …`
 - `npm install`
 - `npm test` (runs all specs)

3. **Join the community**
 - Forum: `https://community.promise-protocol.de`
 - Matrix: `#promise-dev:matrix.org`
 - Monthly GA (members): First Tuesday, 18:00 CET

4. **Make your first contribution**
 - Good first issues: add test cases, improve docs, translate specs, report bugs in merit calc.

---

## FAQ

**Do I need to be a member to contribute?**  
No. Anyone can submit specs/code. Members get voting rights + patronage.

**Can I earn Merit without being a member?**  
Yes. Merit is awarded by adoption/quality, regardless of membership.

**How do I become a member?**  
Apply at the membership page; Board reviews. Minimum share: €500 (see bylaws).

**Can specs change after adoption?**  
Yes. Use versioning (`v1 → v2`). Old versions remain valid until deprecated by class vote.

**What if two specs conflict?**  
Core prevails; Domain Standards must not contradict Core. Experiments remain isolated.

**Where is the exact Merit formula?**  
`governance/merit_calculation.feature` (single source of truth for constants & decay).

**Can I lose Merit?**  
Yes—via time decay and poor outcomes.

**Who decides Core changes?**  
The GA under the reserved-matters rule in the bylaws (concurrent majorities + any GenG super-majorities).

---

## Contact
- Technical: `dev@promise-protocol.de`
- Governance: `governance@promise-protocol.de`
- Membership: `membership@promise-protocol.de`
- Security (PGP on site): `security@promise-protocol.de`

---

## License
- **Protocol specifications:** CC0 (public domain)  
- **Reference code:** see repository license (e.g., Apache-2.0/AGPL-3.0 as applicable)  
- **Documentation:** CC-BY-4.0

By contributing, you agree to these licenses and to the project’s Code of Conduct.

**Build what you believe in—ship what passes the specs.**
