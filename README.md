# C9: Theta(C_7) >= 3.258838705444608, a new lower bound on the Shannon capacity of the 7-cycle

Certificate and exact checker for constant C9 of [teorth/optimizationproblems](https://github.com/teorth/optimizationproblems) ([constants/9a.md](https://teorth.github.io/optimizationproblems/constants/9a.html)).

**Claim.** C_7^(box 680) has an independent set of size M (a 349-digit integer, in `certificate.json`), so Theta(C_7) >= M^(1/680) >= **3.258838705444608**. Previous best: 3.2588326203532663... ([Tan2026], R. Tandon, arXiv:2608.30273, independent set in C_7^(box 500); README value 3.25883262). Gain: about 6.1e-6.

## Construction

Only Tan's ingredients are used. In Tan's Theorem 1 (heterogeneous Gao product) HetGao(L, R)[J0, JH, JV] the codebooks and their counts q depend on the left factor L only, so Tan's certified left patterns can be applied to other right factors R with no new count. Tan's left patterns used: N<S<G15AX,G5,P15A8>,G5>, N<S<G15AX,sG15AX,P15A5>,sG15AX>, N<S<G15AX,sG15Ah,P15A8>,sG15Ah>, N<S<G15X,G10,P15X>,G5>, P10A. Top level: BPZ rule S3b(Phi(g0), Phi(g4), Phi(g8)), then terminal code K4a, giving dimension d = 680. The gadget steps, as stored in the certificate:

```
{"R": "G5", "name": "g0", "op": "hetgao", "pattern": "N<S<G15X,G10,P15X>,G5>"}
{"R": "G5", "name": "g1", "op": "hetgao", "pattern": "N<S<G15AX,G5,P15A8>,G5>"}
{"name": "g2", "of": "g1", "op": "sigma"}
{"R": "g2", "name": "g3", "op": "hetgao", "pattern": "N<S<G15AX,sG15AX,P15A5>,sG15AX>"}
{"name": "g4", "of": "g3", "op": "sigma"}
{"R": "G5", "name": "g5", "op": "hetgao", "pattern": "P10A"}
{"name": "g6", "of": "g5", "op": "sigma"}
{"R": "g6", "name": "g7", "op": "hetgao", "pattern": "N<S<G15AX,sG15Ah,P15A8>,sG15Ah>"}
{"name": "g8", "of": "g7", "op": "sigma"}
```

## Files

| file | SHA-256 |
| ---- | ------- |
| `certificate.json` | `8d55f7465bdedf6b1ea9c4ad3504c1b68c93705500590ff11b6fca66cb9d1f2a` |
| `check_c9.py` | `9591b7f2c53faef015a1043003ce3b48a270bea6d0bec2f42db57d60167349fb` |
| `vendor_tan.sha256` | `1075a446af99d8db5c072e25b41b62fad1f3efc1863e8ca6a92d423ab84b7eb5` |
| `vendor_tan/LICENSE` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| `vendor_tan/NOTICE` | `359e841fec992d2e6df7c44e4e700f94fd1241673a1e10efe15b6dd1787e3a7d` |
| `vendor_tan/SOURCE.txt` | `6282ae93bf869b6724d9dcec58290398d7f3ee69e6d1fd90c5b5999aef9651c6` |
| `vendor_tan/data/base_c7.json` | `2395d9ce16e068010a5f2a57f3fbfec5a607fa9272b02afd6c9e4a95fc70016b` |
| `vendor_tan/data/certificates.json` | `c86f1db7687c3ed9e2a951d602671ce606f1b3830aa8ecf74b7ece069804ebd1` |
| `vendor_tan/data/paper_claims.json` | `a1c85246f777296e81124113d88538a987eee93d712b08e8605b84d1b114677c` |
| `vendor_tan/shannon/__init__.py` | `6f478dacd2650af182e0debb33a339b22ebd09208de42e1ef190136a6fdce31d` |
| `vendor_tan/shannon/bpz.py` | `ded77004630f8a53feaddf87dfab83cc1d93ddb65292367c7d27c4a8dc0f3715` |
| `vendor_tan/shannon/certificates.py` | `96b22141e2d8c6679f4caec37734c8a9e21f52a34dc0492c49b92793b9a1af36` |
| `vendor_tan/shannon/construction.py` | `ce394bd301afee91b416a6934673a34c2eaac9ac760ea6088e493868e15a25fc` |
| `vendor_tan/shannon/counting.py` | `fa85a79814413afdad7d4fc85120f15ae19269c40846c9d8f855dfcd7261d8f8` |
| `vendor_tan/shannon/gadget.py` | `54b30e6992b11983cc321be33dbfd6f6768eadafda4d095cc1caca173c32b2c6` |
| `vendor_tan/shannon/graph.py` | `36a6118783cd5b4963079aa7143f44ab2bbb747576c47202fdce65c91ddae0f9` |

`vendor_tan/` is Tan's verification package, unmodified, at commit c753408492dde92a239708986d16c15dbf6c3235 of https://github.com/tandonravi/C7-Shannon-Capacity-Heterogeneous-Recursion (Apache-2.0; see `vendor_tan/LICENSE` and `vendor_tan/NOTICE`). `vendor_tan.sha256` lists its files. `SHA256SUMS` covers every other file.

## Reproduce (Python 3.9 or later, standard library only)

```sh
sha256sum -c SHA256SUMS
(cd vendor_tan && sha256sum -c ../vendor_tan.sha256)
python3 -I -B check_c9.py certificate.json
```

Measured: 122 s wall time on one core (/usr/bin/python3 (Python 3.12.3), host god, 2026-10-30T12:09:57Z). It uses integers only. It re-derives Tan's certified counts from the 367-word base data, rebuilds Tan's chain at d = 500, evaluates the certificate's expression tree with dimension bookkeeping, re-checks the BPZ rule and terminal code, and proves M^500 > M_Tan^680 and M * 10^(8*680) > 325883262^680. It exits 0 and ends with:

```
CERTIFIED  Theta(C_7) >= M^(1/680) >= 3.258838705444608   (exact: M^500 > M_Tan^680 and M*10^(8*680) > 325883262^680)
PREVIOUS   Theta(C_7) >= M_Tan^(1/500) = 3.258832620353266...   [Tan2026], README value 3.25883262
OK
```

## Provenance and AI use

The search, the certificate and the checker were produced by an AI agent run by Leo Tang. The checker has not been independently re-implemented or formally verified.
