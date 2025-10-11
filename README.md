````markdown
# PROMISE Protocol

**A Mass Online Reasoning & Expertise Marketplace**  
From **ABDUCTIO** (realistic expectations) to **SPONSIO** (verifiable outcomes)

> **Status:** Alpha. Public, evolving spec. Breaking changes possible.

---

## Table of Contents
- [Why PROMISE](#why-promise)
- [What PROMISE Is (and Isn’t)](#what-promise-is-and-isnt)
- [Core Concepts](#core-concepts)
- [Promise Lifecycle](#promise-lifecycle)
- [Roles](#roles)
- [Initial Vertical & Examples](#initial-vertical--examples)
- [Data Model (Illustrative)](#data-model-illustrative)
- [Security, Privacy, and Abuse Prevention](#security-privacy-and-abuse-prevention)
- [Quickstart (Local Dev / Reference Impl)](#quickstart-local-dev--reference-impl)
- [Repository Layout](#repository-layout)
- [Contributing](#contributing)
- [PROMISE Foundation (Co‑operative)](#promise-foundation-cooperative)
- [Licensing](#licensing)
- [Roadmap](#roadmap)
- [FAQ](#faq)

---

## Why PROMISE
The internet made **opinions cheap** and **proof expensive**. PROMISE provides a protocol to **make, audit, and settle promises** about the real world. It connects **transparent reasoning** (ABDUCTIO) to **accountable action** (SPONSIO) so that:

- **Buyers** can purchase outcomes with protection and clarity.
- **Providers** (human or AI) build **portable, domain‑specific reputation** by staking on promises they keep.
- **Communities** can coordinate on **verifiable progress** rather than vibes.

Design goals:
- **Auditability by default** — Every commitment links to its pre‑commit reasoning bundle.
- **Skin in the game** — Staked promises and staked assessments align incentives.
- **Domain specificity** — Reputation (“merit”) is contextual, not generic.
- **Human + AI symmetric** — Same rules for people and agents.
- **Interoperable evidence** — Standard envelopes for success criteria and verification.


## What PROMISE Is (and Isn’t)
**Is:** A protocol and reference implementation for *performance commitments with verifiable outcomes*, backed by auditable reasoning.

**Isn’t:**
- A gambling/prediction site. This is **not** about betting; it’s about **service performance + verification**.
- A replacement for contracts/courts. PROMISE reduces ambiguity and routes disputes; it doesn’t abolish them.


## Core Concepts
- **ABDUCTIO (Pre‑Commit)** — Efficient, auditable reasoning under uncertainty. Produces a decision to commit (or not) with **credence (B)**, **confidence (C)**, and an **evidence plan** gated by EVSI (Expected Value of Sample Information).
- **SPONSIO (Post‑Commit)** — Independent assessment of outcomes against pre‑declared **success criteria**. Assessors stake on judgments; poor judgments are penalized.
- **The Promise (Commit)** — A signed, staked object binding terms, price, success criteria, an evidence schedule, and a link to the ABDUCTIO audit bundle.
- **Merit (Domain‑Scoped)** — Portable, cryptographically auditable reputation that updates from kept/broken promises and assessment quality.
- **Evidence Envelope** — Content‑addressed bundle (hash/CID) containing the baseline, success metrics, and verification artifacts.


## Promise Lifecycle
```text
┌───────────────────────────────┐
│  PRE‑COMMIT: ABDUCTIO         │  Decide IF/HOW to commit
│  • Decompose claim             │  → B (credence), C (confidence)
│  • Plan evidence via EVSI      │  → Evidence schedule & criteria
│  • Produce audit bundle (CID)  │
└──────────────┬────────────────┘
               │ links to
               ▼
┌───────────────────────────────┐
│  COMMIT: THE PROMISE          │  Bind terms + stake + baselines
│  • Sign & post                 │  • Funds escrowed
│  • Baselines frozen            │
└──────────────┬────────────────┘
               │ resolves via
               ▼
┌───────────────────────────────┐
│  POST‑COMMIT: SPONSIO         │  Verify & settle
│  • Assessors stake judgments   │  • Payout / refund / slash
│  • Merit updates (domain)      │  • Feedback to ABDUCTIO
└───────────────────────────────┘
````

## Roles

* **Promisers / Providers** — Make and fulfill promises; stake capital/reputation.
* **Promisees / Buyers** — Purchase outcomes with protection and clear criteria.
* **Assessors** — Independently verify outcomes; stake judgments; earn fees.
* **Template Authors** — Publish reusable domain templates (success criteria, evidence packs).
* **Domain Stewards** — Curate standards, oracles, and guardrails for a domain.

## Initial Vertical & Examples

**Beachhead:** **B2B revenue consulting** — lead with ABDUCTIO’s decision speed & cost savings; offer optional staked outcome promises.

Example templates (illustrative):

* **CAC‑Down 20% in 120 Days** — Domain: `/b2b_saas/acq/cac_blended`
  Success: `CAC_t120 ≤ 0.8 × CAC_baseline` (guardrails on win‑rate).
  Evidence: Ad spend logs, CRM new customers, billing snapshots.
* **+30% Qualified Pipeline in 90 Days** — Domain: `/b2b_saas/pipeline/sql_volume`
  Success: `SQLs_t90 ≥ 1.3 × baseline` with steady win‑rate.
  Evidence: CRM stage transitions.

**Freelancer example (consumer):**
Hypnotherapist promises smoking cessation in 2 sessions.
Success: *30‑day smoke‑free, CO breath test < 6 ppm*.
Stake refunds client if outcome not met; assessor verifies according to pre‑committed criteria.

## Data Model (Illustrative)

> The canonical schemas live in `./spec/schemas/`. Below are fragments for readability.

**Promise (commit object)**

```json
{
  "version": "0.1.0",
  "promise_id": "prm_01J8M2...",
  "promiser_id": "did:key:z6Mk...",
  "promisee_scope": ["did:key:z6Ab...", "org:acme-saas"],
  "domain": "/b2b_saas/acq/cac_blended",
  "terms": {
    "objective": "Reduce blended CAC by 20% in 120 days",
    "timeline_days": 120,
    "price": 80000
  },
  "success_criteria": [
    "CAC_t120 <= 0.8 * CAC_baseline",
    "WinRate_t120 >= WinRate_baseline - 0.02"
  ],
  "evidence_schedule": [
    {"day": 0, "type": "BaselineFreeze", "source": "sfdc+stripe"},
    {"day": 120, "type": "Procedural", "metric": "CAC_blended"}
  ],
  "abductio_audit_cid": "bafybeigdyr...",
  "stake": {"asset": "USD", "amount": 10000},
  "assessment_window_days": 20,
  "signature": "ed25519:..."
}
```

**ABDUCTIO audit (pre‑commit bundle)**

```json
{
  "claim": "Reduce blended CAC by 20% in 120 days",
  "decomposition": [
    "ChannelMixOptimization",
    "LeadQualificationTuning",
    "PricingExperimentation"
  ],
  "credence_B": 0.74,
  "confidence_C": 0.78,
  "evsi_plan": [
    {"test": "MQL→SQL rubric pilot", "cost": 2500, "evsi": 8200},
    {"test": "LP A/B on paid search", "cost": 1200, "evsi": 4100}
  ],
  "evidence_types": ["Direct", "Procedural", "Pattern", "Analogical"],
  "assumptions": ["Stable pricing policy during window"],
  "rivals_ledger": ["Alternative: focus on retention uplift first"],
  "generated_at": "2025-07-19T12:00:00Z"
}
```

**Assessment (post‑commit)**

```json
{
  "assessment_id": "asm_01QZK...",
  "promise_id": "prm_01J8M2...",
  "assessor_id": "did:key:z6Assessor...",
  "judgment": "KEPT",
  "justification": "CAC_t120 = 1,150 vs 1,480 baseline; win‑rate Δ = -0.01",
  "evidence_refs": [
    {"cid": "bafybei...baseline", "type": "BaselineFreeze"},
    {"cid": "bafybei...t120", "type": "Procedural"}
  ],
  "assessor_stake": {"asset": "USD", "amount": 300},
  "signature": "ed25519:...",
  "timestamp": "2025-10-11T09:30:00Z"
}
```

## Security, Privacy, and Abuse Prevention

* **Baseline freeze** at commit; assessors judge only against locked definitions.
* **Overlapping assessor sets** with weight caps; rotation to reduce collusion.
* **Stakes + slashing** for promisers and assessors; minority‑correct guardrails via dispute flows.
* **Least‑privilege connectors**; read‑only exports; content‑addressed evidence bundles.
* **PII minimization**; use aggregates where feasible; consented access only.

## Quickstart (Local Dev / Reference Impl)

> Reference server, SDKs, and schemas are open. ABDUCTIO **Pro** is proprietary and **not** included here.

```bash
# 1) Clone
git clone https://github.com/promise-foundation/promise-protocol.git
cd promise-protocol

# 2) Start dev stack (API + DB + object store mock)
docker compose up -d

# 3) Seed demo data
make seed

# 4) Create a demo promise
curl -X POST localhost:8080/v0/promises \
  -H 'Content-Type: application/json' \
  -d @examples/promise.cac_down_20.json

# 5) Submit an assessment
curl -X POST localhost:8080/v0/assessments \
  -H 'Content-Type: application/json' \
  -d @examples/assessment.kept.json
```

## Repository Layout

```text
.
├─ spec/                # Protocol specs, diagrams, schemas
│  ├─ schemas/          # JSON Schemas (promise, audit, assessment, evidence)
│  └─ rfc/              # Design RFCs (ABDUCTIO, SPONSIO, Merit, Disputes)
├─ api/
│  ├─ openapi.yaml      # Evolving HTTP API
│  └─ server/           # Reference server (TypeScript)
├─ clients/
│  ├─ js/               # JS/TS SDK
│  └─ python/           # Python SDK
├─ packages/
│  ├─ merit-engine/     # Merit math & aggregation
│  ├─ evidence/         # Evidence envelopes & hashing
│  └─ abductio-lite/    # Open ABDUCTIO subset (no Pro features)
├─ examples/            # Sample promises, assessments, templates
├─ docs/                # Guides, ADRs, ethics, governance
└─ tools/               # Dev tooling, linters, generators
```

## Contributing

We welcome contributors aligned with the **PROMISE Code of Ethics** (see `docs/ethics.md`).

* **Discuss:** Open an issue or RFC in `spec/rfc/`.
* **Fork & branch:** `feat/<topic>`; keep PRs focused with tests.
* **DCO:** Use `git commit -s` (Developer Certificate of Origin).
* **Security notes:** If your change touches security, add a short threat note in the PR.
* **Bounties & Patronage:** The PROMISE Foundation operates a **Contribution Ledger** and a quarterly **Patronage Pool** that shares a portion of commercial net revenue with active contributors (providers, assessors, template authors, stewards, community). See `docs/patronage.md`.

## PROMISE Foundation (Co‑operative)

**PROMISE Foundation** is a platform‑cooperative movement to *predict and build the future we want*. It:

* Stewards the open **Promise Protocol**, domain standards, assessor accreditation.
* Maintains the **merit namespace** and public transparency dashboards.
* Funds new domains, templates, and oracles via grants/bounties.

**Revenue model (enables sustainability):**

* **ABDUCTIO Pro** (proprietary): advanced reasoning libraries, EVSI priors by domain, enterprise workflows.
* **Promise Platform SaaS:** hosted features (e.g., transaction processing, assessor routing, SSO, audit exports, data residency).
* **Transaction & assessment fees** on hosted instances.

A portion of commercial net revenue funds the **Patronage Pool** for contributors across roles. Governance details: see `docs/governance.md`.

## Licensing

* **Protocol specs, reference server, SDKs:** Apache‑2.0 (`LICENSE`).
* **ABDUCTIO Pro** & certain SaaS modules: proprietary; **not** included here.
* Trademarks: “PROMISE”, “ABDUCTIO”, and “SPONSIO” are marks of the PROMISE Foundation (see `docs/trademarks.md`).

## Roadmap

* **Q1:** Reference server v0, ABDUCTIO‑Lite, evidence envelopes, assessor portal.
* **Q2:** Merit v1 (recency + stake weighting), dispute quorum, domain dashboards.
* **Q3:** Template marketplace, custom oracles, enterprise audit API.
* **Q4:** Federation of domain councils, internationalization.

Public roadmap: `docs/roadmap.md`.

## FAQ

**Is this a prediction market?**
No. PROMISE implements **performance warranties with verifiable assessments**, not betting.

**Can AI agents participate?**
Yes—under the same staking, evidence, and merit rules as humans.

**What happens in disputes?**
Pre‑committed rules + rotating assessor quorum + appeals. See `spec/rfc/002-disputes.md`.

**How do you prevent moving the goalposts?**
Baselines and success criteria are **frozen at commit**; assessors judge against those definitions only.

**How does the cooperative pay contributors?**
Direct earnings (services/assessments/template usage) + quarterly **Patronage Pool** distributions based on the **Contribution Ledger**. Details in `docs/patronage.md`.

**Where should I start?**
Read `docs/ethics.md`, explore `examples/`, then try the Quickstart to create a demo promise.

---

**Build with us. Keep your promises.**

```
```
