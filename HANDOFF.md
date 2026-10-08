# Codexクラウドへの引継ぎ

2026年10月8日。定理3.2・系5.2は**未証明、形式的な定理文も未実装**です。

既存の線形RightModuleの定義を保ち、一般radical・minimality、有限AS分解、
実際のExtのk線形性と次元シフト、原論文のAS条件を具体化しました。
既存presheafモデルのASRegularから実際のExt³(s_(tau v),P_v)≃ₗ[k]kと、
他の全Extの消滅・delta型の次元公式・有限台の表まで証明しました。
これは命題1.3の数値的順方向です。左加群としてのAS双対性や周期性、主定理の完成ではありません。

## 場所・固定環境・権限

- リポジトリ：https://github.com/uedakazushi/as-ginzburg-lean 。作業場所：`/workspace/as-ginzburg-lean`。
- ブランチmain。最新の明示的な指示は自律的な継続と、検証済み単位の直接mainへの保存。新規PRなし。
- 前回までのmain d928bafから継続。旧「mainへマージしない」制約はユーザーの明示的な指示で置き換え済み。
- Lean：leanprover/lean4:v4.24.0。mathlib：f897ebcf72cd16f89ab4577d0c826cd14afaafc7。manifest全依存を固定。
- 原論文の仮定を弱めず、周期性・必要なExt同型・主定理相当の結論を追加仮定にしない。

## 今回完成した14単位

1. 一般radicalの右作用閉性・自然性・線形functor。
2. 像のradical包含としてのminimality、因子化との同値、合成の閉性。
3. s_iのradicalが零、最小微分にHom(-,s_i)を適用すると零。
4. (1.6)の四項・有限coproduct・微分・exactness・Mono・minimalityの具体的ASResolution。
5. 標準導来圏の線形性、実際のAbelian.Extのk作用、0次Homの元の作用との一致。
6. 有限ASResolutionからmathlib ProjectiveResolution、augmentationのQuasiIso、degree≥4の零。
7. 分解の存在と全Extの総Cardinal rank=1による具体的ASRegular。各Extの有限次元性。
8. 実際のHom複体、Hom(-,s_i)の零微分とホモロジーの同定。
9. s_(tau v)の分解へのHom(-,P_v)の各項0,0,0,k。
10. 実際のExtのYoneda積双線形性、長完全列の線形connecting map・dimension shift。
11. このHom複体のH³≃k、他の次数のIsZero。
12. AS分解の二つのkernelへのepi coverと三つのsyzygy短完全列。
13. 三段のdimension shiftから実際のExt³(s_(tau v),P_v)≃k。
14. 総rank=1から他のExt消滅、(1.11)の数値的順方向、実際のfinrankの有限台表。

原論文との対応・mathlib API・利用先はdocs/as_resolution_ext_bridge.md。
ASResolutionの存在は原論文定義(i)の条件であり、任意のAで成立するという定理は未証明。
ASRegularは任意Propの入力でなく実際の分解と実際のExtから定義した条件。
周期性・delta型のExt表をAS定義に追加していない。tauは頂点置換のまま。
基盤補題が一般の体で成立しても、主定理の代数閉・標数0を弱めたとは扱わない。

## 現在の検査

最新ローカル検証 `20261008T031342Z-13ba299c`：全段階終了0、161.737727秒。
UTC 2026-10-08T03:13:42.658554+00:00 → 2026-10-08T03:16:24.396290+00:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。

35数学モジュール、369異なる明示的宣言、177 theorem、53 named instanceを監査。
ソースにsorry/admit/独自axiomなし。公理依存はpropext、Classical.choice、Quot.soundのみ。
sorryAx、Lean.ofReduceBool、Lean.trustCompilerへの依存なし。
新規数学ファイルに未解決のコンパイルエラー・lint警告なし。既存のlint警告は残存。
161は初期成果の件数で、宣言数の固定条件ではありません。

## 保存と次の検証

各証明単位はruns/radical-resolution-20261008-unit*.patchと新規verification/runs/に保存。
実測時刻・終了コード・次の義務・main保存先はruns/radical-resolution-20261008.mdとRECENT_RUN.md。
初期14数学モジュール・入力PDFの旧SHA-256一致、recovery/とcheckpoints/の無変更を再確認。
保存確認はverification/radical_resolution_preservation.json。ルートimportと生成AxiomAuditは意図した更新。
CLI git pushの認証エラー(終了128)後、接続済みGitHub APIへ切り替えた。
ローカル検証済みtreeのSHA一致とexpected_shaを確認し、force=falseでmainを通常のfast-forward保存。
ローカルmainも同じAPI commit objectに同期。CLIの認証が修復されたという主張はしない。
新規PRなし。mainへのpush・最新Actionsとartifactの確認はRECENT_RUN.md参照。

```bash
USE_FRO_CACHE=1 AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux \
  bash scripts/check.sh --prepare-cache
```

キャッシュがあれば--prepare-cacheを省略。通常の再現でlake updateは不要。
CIはpush/pull_requestごとに同じ固定環境の検証を実行し、今回のログをartifactに保存する。

## 次に必要な証明義務

- 原論文の局所単位元付き直和加群Gr(A)と既存presheafモデルの明示的同値、Ext保存。
- 全M,N・全次数の自然なHom複体–Abelian.Ext比較。命題1.3の3次比較は証明済み。
- (1.11)→(1.7)の逆方向。finrankだけでは無限次元を排除できないので有限性を省かない。
- A-dualの左加群作用、有限生成分解と直和の交換、(1.12)の左加群AS双対性。
- 有限長双対性、区間同型のcoherence、AS条件からの周期性。WindowSystemをAS条件に加えない。
- 特定のJacobian代数についてAS分解の存在、Jacobian商とGinzburg dg代数、外部一般定理、主定理の同型類対応。

命題1.4は区間同型を仮定した貼り合わせのみ、命題5.1も未証明。
過去の稼働時間は不明。今回の実測区間・開始終了・所要時間はタスク記録参照。
