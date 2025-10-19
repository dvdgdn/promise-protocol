# CONTRIBUTING-POST-INCORPORATION.md — Proof-of-Contribution & Compensation
**No tokens. No wallets. No surprises.**

This document is the **front door for contributors** (engineers, designers, researchers, etc). It explains **what work we pay for, how it’s accepted, when you get paid**, and how **Proof-of-Contribution (PCR) units** work for upside sharing and governance weight.

---

## TL;DR
- We pay **cash** for accepted work at posted rates **and** mint **PCR units** (internal, non-transferable contribution credits) that determine your share of any **profit pools** and **domain governance weight**.
- **Not money, not tokens, not redeemable, not transferable.** PCR exists **only** inside this cooperative per the bylaws.
- Every task has a **Promised Deliverable** card with **frozen acceptance tests**, named **assessor** + **backup**, and a clear **price** and **deadline**.

---

## 0) What you get

**1) Cash compensation (invoice)**
- Posted rate per task/issue/milestone.
- **Payment timing:** paid within **7 days** of acceptance (SEPA/ACH), unless otherwise stated.

**2) PCR units (Proof-of-Contribution)**
- Minted **only** on accepted work.
- Used for:  
  - **Profit distributions** (if profits exist and the Board/GA approves), and  
  - **Domain governance weight** (Merit) under class rules/caps.  
- **PCR is not** money/equity/token; **no wallet, no resale, no cash-out**.

---

## 1) How work is defined (no moving goalposts)

Every paid task includes a **Promised Deliverable** card with frozen scope & tests:

    promise:
      id: prm-evsi-001
      title: "EVSI calculator (Beta–Bernoulli) v0.1"
      scope:
        - CLI + library function
        - Inputs: a,b, utilities (TP/FP/TN/FN)
        - Outputs: EVSI value, decision recommendation
      acceptance_tests:
        - unit: tests/evsi_bernoulli.spec.ts (≥95% pass)
        - perf: 10k evaluations < 1s on target machine
        - docs: README section with 2 examples
      price_cash: "€2,500"
      pcr_band: "base 250 units"
      deadline: "2025-11-15T23:59:59Z"
      assessor: "@maintainerA"
      assessor_backup: "@maintainerB"

If anything material changes, we **issue a new promise card** (new ID). No silent scope creep.

---

## 2) Acceptance & independence

**Process**
1. You submit the PR. CI must pass.  
2. **Assessor** checks against the acceptance tests.  
3. If accepted → **cash payable** + **PCR minted**.  
4. If rejected → you receive written reasons (linked to the tests). You may **appeal** to the **backup assessor** within **7 days**.

**SLAs**
- Backup assessor responds within **3 business days** to appeals.
- We keep an **append-only decision log** (accept/reject, reasons, timestamps).

**Independence & conflicts**
- Assessors **cannot** review their own commits or those of **direct reports**.
- We rotate assessors; overturn rates are tracked. High-overturn assessors lose privileges during a cooling-off period.

---

## 3) PCR minting (the exact math)

When accepted, we mint a signed PCR receipt:

    {
      "pcrId": "pcr_01HXQ…",
      "contributor": "did:key:z6M…",
      "promiseId": "prm-evsi-001",
      "domain": "/platform/engineering/core",
      "base_units": 250,
      "quality_score": 0.92,      // tests, review, defect rate
      "impact_score": 1.30,       // usage unlocks, adoption, service criticality
      "time_decay": 1.00,         // exp(-λ * age_months); λ=0.1 default
      "final_units": 299.0,       // base * quality * impact * decay
      "evidence": ["commit:abc123", "ci:build#456", "docs:README@f1a2"],
      "assessor": "did:key:z6Assessor…",
      "signedAt": "2025-11-02T10:15:31Z"
    }

**Formula (public, fixed in repo)**
- final_units = base_units × quality_score × impact_score × exp(−λ × months_since_accept)

**Defaults**
- quality_score ∈ [0.70, 1.00]  
- impact_score ∈ [0.80, 1.50]  
- λ = 0.10 (≈ 6–7 month half-life)

All constants live in a single config (`docs/pcr.md`) and are referenced by the monthly report.

**What PCR is NOT**
- Not currency, equity, token, voucher, or stored value.  
- Cannot be bought/sold/transferred/redeemed.  
- Exists solely to split approved profit pools and weigh domain governance votes (subject to cooperative caps).

---

## 4) Profit distributions (if profits exist)

At month-end, we compute **Distributable Profit (DP)**:

    DP = Revenue − COGS − Operating Expenses − Reserve(30%)

Pools are set by the Board/GA (illustrative ranges):
- **Labor contributors:** 60–70% of DP  
- **Customer contributors:** 10–15%  
- **Capital contributors (capped):** 10–15%  
- **Community fund:** 10–15%

Your payout from the **labor pool**:

    payout_i = (VU_i / Σ VU_all) × LaborPool
    where VU_i = Σ final_units from your PCRs (after decay)

**Example**  
LaborPool = €65,000; Your VU = 2,900; Total VU = 85,000 → Your share ≈ **€2,216**  
(…in addition to your already-paid cash invoice.)

Distributions depend on **actual profits** and formal approval per bylaws.

---

## 5) Payments & reporting

**Cash for accepted work**  
- Invoice upon acceptance; **paid within 7 days** via SEPA/ACH.

**PCR report (monthly)**  
- Every PCR line item (ID, base, quality, impact, decay, final units)  
- Pool sizes + exact distribution math  
- Assessor rotation/overturn metrics  
- We publish a **Merkle root** of receipts for verifiable totals without exposing private data.

**VAT & invoicing notes (EU)**
- B2B EU: include your **VAT ID** where applicable; reverse-charge rules may apply.  
- Place-of-supply follows service nature/jurisdiction; we reflect this on invoices.

---

## 6) How to start (fast path)

1. Read this file and `CODE_OF_CONDUCT.md`.  
2. Sign the short **Contributor Agreement** (DCO + IP grant; link in repo).  
3. Pick an issue labeled **good-first-issue** or **bounty**.  
4. Get a **promise card** (like above) with **price + PCR band + tests**.  
5. Build → PR → CI green → review.  
6. Acceptance → invoice → **cash in 7 days** → **PCR minted**.

Prefer design docs first? Open an **RFC issue**; small PCR is available for accepted design work.

---

## 7) Paid examples we’re commissioning

- **Merit engine**: dependence-aware aggregation (log-opinion pool; overlap penalties)  
- **EVSI methods**: RISK/VARSIZE implementations + unit benchmarks  
- **Evidence hashing**: content-addressed envelopes + DSSE signatures  
- **Assessor portal**: rotation rules, N_eff diagnostics, appeal UI  
- **Reference verifier**: CLI that recomputes public metrics (Wilson LB, TR) from JSON  
Each item will have a **promise card** with price, tests, and PCR band.

---

## 8) Disputes & fairness

- **Appeal window:** 7 days from rejection; backup assessor decides within **3 business days**.  
- **Conflicts:** assessors can’t accept work they authored or for direct reports.  
- **Overturn tracking:** frequent overturns remove assessor privileges temporarily.  
- **Transparency:** decision log is append-only and reviewable.

---

## 9) Legal & licensing (plain language)

- **Open source:** Protocol specs, reference server, SDKs → see repo license (Apache-2.0/AGPL-3.0 as applicable).  
- **Closed modules:** Some commercial modules (e.g., ABDUCTIO Pro) may be proprietary.  
- **No tokens / securities:** We do **not** issue tokens. PCR units are internal credits only.  
- **Tax:** Cash payments are standard contractor invoices; you handle your tax obligations.

IP terms and DCO are in the **Contributor Agreement** linked in this repo.

---

## 10) FAQ (engineer-friendly)

**Is PCR “equity by another name”?**  
No. Not equity or a security. PCR is an internal, non-transferable credit for sharing approved profit pools and determining domain governance weight under caps.

**When do I get actual money?**  
On acceptance: you invoice for the posted rate; we pay **within 7 days**. Profit distributions (if any) are extra.

**Who sets my quality/impact scores?**  
The assessor, using a public rubric (`docs/pcr_rubric.md`). You can see, question, and appeal them.

**What if there’s no profit?**  
Then there’s no distribution that month—you still got paid cash for accepted work.

**Can I transfer or sell my PCR?**  
No. PCR is non-transferable and has no cash value.

**Can I see real examples?**  
Yes: `reports/pcr/YYYY-MM.md` shows anonymized receipts, scores, and pool math.

---

## 11) PCR receipt schema (for the curious)

    {
      "$schema": "https://example.org/schemas/pcr.schema.json",
      "pcrId": "string",
      "contributor": "did:key…",
      "promiseId": "string",
      "domain": "string",
      "base_units": "number",
      "quality_score": "number",
      "impact_score": "number",
      "time_decay": "number",
      "final_units": "number",
      "evidence": ["string"],
      "assessor": "did:key…",
      "signedAt": "RFC3339"
    }

---

## 12) Contacts

- Maintainers: `@maintainerA`, `@maintainerB`  
- Security (PGP on website): `security@project.example`  
- Ops & invoices: `ops@project.example`  
- General: `dev@project.example`

---

### Short promise of fairness (human-readable)
We define work up front, test against clear criteria, **pay promptly** for accepted work, and publish the math behind contribution credits and any profit shares. **No tokens. No dilution. No moving goalposts.**
