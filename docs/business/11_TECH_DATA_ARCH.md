# 11) Tech & Data Architecture

**Plain idea:** simple rails, strong guarantees. We favor boring, proven components; every important decision leaves a small, readable artifact (PDF/JSON), and money only moves through licensed PSPs.

---

## System shape (mental map)

**Clients**
- Web app (providers, reviewers, clients)
- Public “Proof Pages” (per domain)
- Partner console (reviewers/coaches)

**Services**
- **Domain Registry** — namespaces & standards (N/S), parameters, versions
- **Template Service** — promise templates (compose multiple N/S standards)
- **ABDUCTIO Engine** — turns a claim into *(Credence, Confidence)* + rationale
- **Decision Engine (SPONSIO)** — evaluates pass/fail rules, emits a Decision
- **Evidence Service** — diaries, scales, check-ins, file uploads, timestamps
- **Payments Adapter** — PSP authorize→capture/refund; idempotent webhooks
- **Virtual Credits** — issuer-only Report Passes/Vouchers (closed loop)
- **Identity** — basic→`kyc1` levels, signatures, reviewer sealing
- **Export Service** — one-page Decision Export (PDF/JSON); VC issuance
- **Merit & Scores** — non-monetary domain merit; domain-scoped performance

**Storage**
- Postgres (primary) + Redis (cache/queues)
- Object storage for evidence (EU region), content-addressed
- Append-only **Event Log** for audit & replay

**Observability**
- Metrics (kept-rate, auto-decision %, disputes %, latency)
- Structured logs; audit hashes; alerting on PSP/webhook failures

---

## The data model (what we actually store)

| Entity | What it holds | Notes |
|---|---|---|
| **Agent** | provider / reviewer / client | class & membership flags |
| **Namespace** | `/coaching/sleep` | hierarchy & inheritance |
| **Standard** | `/_twoSessionISIImprovement` | parameters & version (e.g., `_..._v2`) |
| **TemplateVersion** | composition of N/S + ranges | human-readable copy + machine spec |
| **Promise** | who, what, when; parameters | references TemplateVersion & standards |
| **Evidence** | diary/scale entries, files | time-stamped; minimal PII |
| **Decision** | pass/fail + reason | hash of inputs; signer; timestamps |
| **Outcome** | KEPT / NOT KEPT | linked to Decision |
| **PaymentAuth** | PSP ids, amounts | never card data; status transitions |
| **Voucher** | Report Pass (Virtual) | issuer-only; redeemable for ABDUCTIO exports |
| **MeritEvent** | adoption × quality | non-monetary; domain-scoped |
| **DomainScore** | per-agent performance in N | Wilson bounds, recency weighting |
| **IdentityCheck** | level, doc refs | used to gate sensitive actions |

All important records include a **content hash** (`sha256`) and **provenance** (who/when/version).

---

## ABDUCTIO Engine (pre-commit)

**Goal:** produce two numbers and a short, auditable justification.

1) **Decompose the claim** into sub-claims (method works, fit for you, adherence, measurement validity).  
2) **Gather evidence** (citations, prior outcomes, your self-inputs).  
3) **Score sub-claims** → **Credence** (probability) + **Confidence** (stability of that estimate).  
4) **Stopping rule:** enough investigation for the stakes (suggest one more check only when the expected value of info beats its cost).  
5) **Export:** one-page summary (PDF/JSON) with the tree, the numbers, and a clear recommendation.

**Reproducibility**
- Snapshot **model version**, **prompt**, **parameters**, and **inputs**.
- Deterministic mode where possible; include random seeds and cache keys.
- Store a compact **Rationale Trace** (bulleted, source-linked) so a reviewer can spot-check.

> ABDUCTIO stands alone. You can run it for any decision; SPONSIO is optional.

---

## Decision Engine (SPONSIO, post-commit)

**Goal:** settle on pre-agreed outcomes, not opinions.

- **Rule registry:** templates reference concrete pass/fail standards (e.g., `/coaching/sleep/_twoSessionISIImprovement{isi_delta:6, window_days:14}`).
- **Evaluate:** when evidence lands (e.g., final ISI + diary), compute result → **Decision = KEPT/NOT KEPT** with reason (“met Path A threshold”).  
- **Emit:** Decision event triggers **Export** (PDF/JSON), **Payments Adapter** (capture/refund), and **DomainScore** update.

**Disputes**
- Most resolve automatically. If contested, open a **neutral review window** (e.g., 7 days) with a single-page evidence pack.
- Time-boxed; outcomes logged; template adjustments flow back to future versions.

---

## Payments (Earnest) — no custody, ever

- **Authorize** success component at start; base fee captured per coach settings.
- On Decision: **capture** or **refund** the success component.
- **Webhooks**: idempotent handlers for auth/capture/refund; retry with backoff.
- **Windows**: if holds expire for longer programs, use **capture + auto-refund** method.
- **Language:** product & ToS explicitly “payment-timing tool,” **not** “escrow/wallet.”

---

## Virtual Credits (Report Passes) — closed loop

- **Issuer-only vouchers** redeemable **only** for ABDUCTIO exports.  
- No cash-out, no P2P, no EUR peg (limited-network posture).  
- **Counters** track 12-month volume against thresholds; labels are plain (“Report Pass”).  
- Accounting: deferred revenue → recognized at redemption.

---

## Identity & signatures

- **Levels:** `basic` (browse), `kyc1` (sign exports, capture success fees).  
- **Reviewer sealing:** ABDUCTIO viability exports can be issued as **W3C Verifiable Credentials** (JSON-LD + JWS).  
- **PDFs** include a QR deep-link to an online verifier that checks the hash + signature.

---

## Evidence instruments (MVP)

- **Sleep:** ISI + 7-day consensus diary (primary); wearable optional (supporting, not decisive).  
- **Smoking:** daily nicotine check-ins; optional cotinine test.  
- **Web:** PageSpeed run + acceptance test suite.

**Design rules**
- Prefer **structured-subjective** over pure vibes; make **primary vs supporting** explicit.
- Store **means/medians** over windows; no “best night” screenshots.

---

## Security & privacy (by default)

- **Hosting:** EU region; encryption in transit (TLS) and at rest (AES-256).  
- **Secrets:** vault-managed; short-lived tokens; least-privilege roles.  
- **PII minimization:** store only what the template needs.  
- **Erasure/redaction:** remove PII; keep non-personal **hash trails** for integrity.  
- **Access controls:** role-based + domain-scoped; reviewer data separated from client journals.  
- **DPIA & LIAs:** documented lawful bases (contract for Earnest; legitimate interests for reputation with balancing test).  
- **DSA basics:** terms, notice-and-action, searchable transparency page.

---

## Observability & resilience

- **Health:** latency on decision paths; webhook success rate; export failures (<1%).  
- **Quality:** auto-decision %, dispute %, adherence rates, instrument completion %.  
- **Anti-gaming:** small-n flags, Wilson lower bounds, recency weighting, repeated-pair down-weighting.  
- **Backups:** daily db snapshots; object storage versioning; restore runbooks.  
- **Idempotency:** everywhere a webhook or export can double-fire.

---

## How we add a domain without breaking things

1) Register **2–5 standards** (`/_name`) under a sensible namespace.  
2) Draft a **TemplateVersion** that references those standards + cross-domain rails (`/verification/_evidenceExportProvided`, `/payments/timing/_authorizeCaptureRefund`).  
3) Plug in instruments (forms, validators) → small pilot → publish.  
4) Version to `_name_v2` for changes; keep v1 valid until sunset.

No new microservice; mostly **metadata + spec tests**.

---

## What we deliberately aren’t building (MVP)

- No wallets, no custody, no “escrow.”  
- No transferable or cash-redeemable tokens.  
- No black-box decisions: every decision has a **one-page export** a human can read.  
- No heavy on-chain dependency (we can add attestations later if a partner needs them).

---

## A Decision Export (one page, every time)

- **Who/what:** parties, template, standards, parameters  
- **Baseline & follow-up:** key numbers, windows, adherence  
- **Rule evaluated:** Path A / Path B, thresholds  
- **Result:** KEPT / NOT KEPT, reason string  
- **Hashes & signatures:** evidence hash, export hash, signer, timestamp  
- **QR link:** verify online → shows the same summary + signature status

This is the artifact your skeptic reads and says, “Okay, fair.”

---

## Stack notes (boring on purpose)

- **API & workers:** TypeScript/Node (fast iteration), Python workers for instruments if needed.  
- **DB:** Postgres (schemas per module), Redis (queues/cache).  
- **Infra:** containers + IaC; blue-green deploys; feature flags.  
- **Docs-as-specs:** templates and standards stored as text + tests; CI runs spec checks on every change.

**Bottom line:** small, readable pieces that prove every step. Decisions are reproducible; money moves only through licensed rails; privacy is respected; adding domains is mostly configuration—not a rebuild.
