# Cryptography and security results: index and scope

Scope: every cryptographic or security claim stated as a result in the work behind this repository.
Each row is either proved in Lean (file and main theorems) or listed as out of scope with the reason.

## Proved

| Claim | File | Main theorems |
|---|---|---|
| One-time pad: ciphertext uniform and independent of plaintext | `scratch/crypto/PerfectSecrecy.lean` | `key_unique`, `ciphertext_uniform`, `perfect_secrecy` |
| Perfect secrecy (uniform-key form) needs at least as many keys as messages | same | `shannon_key_bound`, `otp_meets_bound` |
| Three-share XOR secret sharing: any two shares are uniform, all three open | `scratch/borromean/Borromean.lean` | `pair_shares_uniform_*`, `three_shares_open` |
| Bell–LaPadula: information flows only up | `scratch/crypto/LatticeFlow.lean` | `blp_flow_up`, `write_down_leaks` |
| Biba is Bell–LaPadula on the reversed order | same | `biba_eq_blp_dual`, `biba_flow_down` |
| Enforcing both gives isolation | same | `isolation` |
| Bell–LaPadula and Biba form a CoCo pair: shared part = isolation, conflict part = direction | `scratch/crypto/BLPBibaCoCo.lean` | `coco_of_policies`, `coco_policies_unique`, `shared_eq_one_iff`, `conflict_pos_iff` |
| CoCo is the fixed/negated split of the payoff-swap involution | `scratch/crypto/LatticeFlow.lean` | `involution_split`, `involution_split_unique`, `coco_is_swap_split` |
| Averaging is the unique symmetric projection; a symmetric pick can fail to exist; picking uses choice | `scratch/crypto/AverageOrPick.lean` | `averaging_unique`, `no_symmetric_pick`, `pick_exists` |
| Events two parties can agree on are the cells of the join of their partitions | `scratch/crypto/CommonKnowledge.lean` | `common_iff_join`, `connected_no_common`, `example_disagree` |
| BB84: same basis certain, other basis a fair coin, intercept-resend error 1/4 | `scratch/crypto/BB84.lean` | `same_basis`, `unbiased`, `intercept_resend_error` |
| Sifting: matching bases share the bit, mismatched bases are independent, key rate 1/2 | `scratch/crypto/Sifting.lean` | `agree_prob`, `sifted_bits_match`, `mismatched_independent`, `key_rate` |
| Cut-and-choose auditing: escape count C(n − t, k) | `scratch/crypto/CutAndChooseAudit.lean` | `escape_count`, `escape_one_bad` |
| Finite de Finetti; two posted-price agents are jointly unexploitable iff they post the same probability vector | `scratch/crypto/DutchBook.lean` | `coherent_iff`, `arbitrage_of_disagree`, `joint_coherent_iff` |
| Identical deterministic agents cannot elect a leader; coins break ties at rate (1/2)^k | `scratch/crypto/SymmetryBreaking.lean` | `no_deterministic_leader`, `tie_fraction` |
| Fiat–Shamir: simulation without the secret, special soundness, forgery from a self-referential fixed point | `scratch/crypto/FiatShamir.lean` | `simulate`, `special_soundness`, `one_challenge_without_secret`, `fs_fixed_point_forgery` |
| Feistel rounds and Feistel ciphers are even permutations (halves ≥ 2 bits); tight | `scratch/cipher/FeistelEven.lean` | `sign_feistel`, `feistel_cipher_mem_alternatingGroup`, `feistel_zero_one_bit_odd`, `zmod4_odd_round` |
| AES-shaped SPN ciphers are even permutations; tight | `scratch/cipher/SPNCipherEven.lean` | `sign_cipher`, `closure_rounds_le_alternatingGroup`, `exists_odd_round_two_one` |
| Layer lemmas: copies, transvections, GL(n, 2) even for n ≠ 2 | `scratch/cipher/TensorSignA.lean`, `TransvectionSignB.lean`, `LinearLayerSignB.lean` | `sign_copies`, `sign_layer`, `sign_linearEquiv_eq_one_of_three_le` |
| The sign is a one-bit probe blind to ciphers; evaluation separates; kernel = what a representation cannot feel | `scratch/cipher/ParityProbe.lean`, `RepresentationKernelB.lean` | `sign_probe_blind`, `eval_probe_separates` |
| Perfect obfuscation = canonical forms; none computable for Turing-complete programs; no-cloning | `scratch/obfuscation/ObfuscationNP.lean` | `perfectIO_decides`, `no_computable_perfectIO`, `no_cloning`, `basis_cloning` |
| OLPC Bitfrost mechanisms: no prompts, key continuity, leases (also a kill switch), developer-key delay | `scratch/bitfrost/Bitfrost.lean` | `requests_change_nothing`, `impostor_detected`, `first_use_blind`, `cut_off_unusable` |
| Sealed records test forecasts; hindsight cannot | `scratch/sealed/SealedEnvelope.lean` | `hindsight_blind`, `seal_separates`, `binding_bound` |
| Side channels: an invariant survives the disguise | `scratch/sidechannel/LoShu.lean` | `parity_invariant`, `label_not_invariant` |
| Locality: outside cannot tell inside apart until a signal arrives, and vice versa | `scratch/automata/LightCone.lean` | `light_cone`, `inside_hidden`, `outside_hidden` |

| Cheap talk: aligned senders transmit; opposed senders only babble; a powerless channel's guarantee equals no channel | `scratch/crypto/CheapTalk.lean` | `aligned_truthful_equilibrium`, `opposed_only_babbling`, `powerless_policy`, `every_listening_policy_exploitable` |
| Bell–LaPadula and Biba invariants over traces; taint creep; robust declassification (earlier, independent formalization) | `scratch/infoflow/BellLaPadula.lean` | `trace_inv`, `basic_security`, `no_flow_down`, `basic_security_reads_free` |
| Dutch book on a finite partition (earlier, independent formalization) | `scratch/atlas2/A07_dutch_book.lean` | `dutch_book_iff`, `dutch_book_iff_nonempty` |
| Money-pumping discretizers; Sybil extraction bound | `scratch/DiscretizePump.lean` | `memoryless_pumpable`, `ef_unpumpable`, `sybil_extraction_le` |
| Reproductive value as the unique no-arbitrage exchange rate (Perron–Frobenius) | `scratch/offers/PerronReproductiveValue.lean` | `exists_pos_left_eigenvector`, `left_eigenvector_unique` |
| Racing runner-up versions of the layer lemmas | `scratch/cipher/TensorSignB.lean`, `LinearLayerSignA.lean`, `TransvectionSignA.lean`, `RepresentationKernelA.lean` | same statements as the winners |

## Completeness check

Every Lean file in the repository was scanned for security terms (cipher, encryption, secrecy, secret sharing,
one-time pad, obfuscation, eavesdropping, Fiat–Shamir, Bell–LaPadula, Biba, BB84, Dutch book, arbitrage, key
continuity, side channel, commitment, hash collision, leader election, cut-and-choose). Every matching file is
cited above, except these, which match only in a non-security sense:

| File | Why it matched | Topic |
|---|---|---|
| `scratch/SpatialMarketStatements.lean` | "arbitrage" in a market model | spatial markets, AM–GM as KL |
| `scratch/control/ControlIsResponsiveness{A,B}.lean` | "commitment" | control as responsiveness |
| `scratch/infovalue/AcausalBlackmail.lean` | "commitment" | decision theory (act vs policy credit) |
| `scratch/rock/RockCommitment{A,B}.lean` | "commitment" | game-theoretic commitment in Chicken and RPS |
| `scratch/sources/F4_price_replicator_bayes.lean` | "arbitrage"/selection terms | Price identity, replicator = Bayes |

## Out of scope, with reasons

| Claim | Status | Reason |
|---|---|---|
| DES and AES round functions generate the whole alternating group (Wernsdorf 1993, 2002) | cited | Large group-generation proofs; only the inclusion into the alternating group is proved here |
| Computational security (IND-CPA, reductions to hard problems) | not formalized | Needs a probabilistic polynomial-time adversary framework not built here |
| Fiat–Shamir insecurity for every concrete hash (Goldwasser–Kalai 2003) | cited | The full construction is large; the fixed-point mechanism is proved |
| Indistinguishability obfuscation from well-founded assumptions (Jain–Lin–Sahai 2021) | cited | Depends on cryptographic hardness assumptions |
| Quantum copy-protection (Aaronson 2009 and later) | cited | Only the no-cloning kernel is proved |
| Perfect secrecy for non-uniform key distributions (Shannon 1949, full form) | cited | Only the uniform-key counting form is proved |
