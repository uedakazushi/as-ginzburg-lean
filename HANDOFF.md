# Codexクラウドへの引継ぎ

有限coproductのHom交換、実際のExtの自然な接続写像・次元シフト・余核表示に加え、
核・余核による交換の閉性とHomの自然な核表示を証明しました。
小さい直和のexactnessは加群圏から導いています。次は有限AS分解に適用して全次数Extの交換を検査します。
Gr(A)比較・周期性と主定理は未証明です。
最新ローカル検証 20261008T052948Z-7fa5cc82：55数学モジュール・546異なる宣言・231 theorem、全段階終了0。
単位1〜3の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/ext-sums-20261008.md。

2026年10月8日。定理3.2・系5.2は**未証明、形式的な定理文も未実装**です。

既存の線形RightModuleを保ち、有限AS分解だけから全次数のExt(s_w,P_i)の有限性と次数4以上の消滅を証明しました。
有限AS分解の存在の下で、元のASRegularと式(1.11)の数値条件の両方向の同値が証明済みです。
具体的な左加群・A-dual・左単純商を構成し、実際のExt(s_w,P_i,p)の成分左加群が
p≠3で零、p=3でs^left_(tau^{-1}w)に同型であることを左作用ごと証明しました。
Hom(P_i,-)・Ext⁰(P_i,-)の余極限交換、左側の射影性・EnoughProjectives・実際のExtの存在も完成しました。
左A-dualも構成し、左右のrepresentableが二重A-dualで元に戻る同型を証明しました。
原論文のExt(s_w,A)への直和交換、Gr(A)比較、周期性と主定理は未証明です。

## 場所・固定環境・権限

- リポジトリ：https://github.com/uedakazushi/as-ginzburg-lean 。作業場所：`/workspace/as-ginzburg-lean`。
- ブランチmain。最新の明示的な指示は自律的な継続と、検証済み単位の直接mainへの保存。新規PRなし。
- 今回はmain a3debe1から継続。以後の保存先はRECENT_RUN.md参照。旧制約は最新の直接main保存の指示に置き換え済み。
- Lean：leanprover/lean4:v4.24.0。mathlib：f897ebcf72cd16f89ab4577d0c826cd14afaafc7。manifest全依存を固定。
- 原論文の仮定を弱めず、周期性・必要なExt同型・主定理相当の結論を追加仮定にしない。

## 前回までに完成した14単位

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

最新ローカル検証 `20261008T050918Z-e404c546`：全段階終了0、232.167668385秒。
JST 2026-10-08T14:09:18.501217+09:00 → 2026-10-08T14:13:10.668891+09:00。
UTC 2026-10-08T05:09:18.501217+00:00 → 2026-10-08T05:13:10.668891+00:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。

53数学モジュール、529異なる明示的宣言、227 theorem、100 named instanceを監査。
ソースにsorry/admit/独自axiomなし。公理依存はpropext、Classical.choice、Quot.soundのみ。
sorryAx、Lean.ofReduceBool、Lean.trustCompilerへの依存なし。
新規数学ファイルに未解決のコンパイルエラー・lint警告なし。既存のlint警告は残存。
161は初期成果の件数で、宣言数の固定条件ではありません。

## 保存と次の検証

今回の証明単位はruns/as-finiteness-20261008-unit*.patchと新規verification/runs/に保存。
前回のruns/radical-resolution-20261008-unit*.patchも保持。
今回の実測時刻・終了コード・次の義務・main保存先はruns/as-finiteness-20261008.mdとRECENT_RUN.md。
初期14数学モジュール・入力PDFの旧SHA-256一致、recovery/とcheckpoints/の無変更を再確認。
今回の保存確認はverification/as_finiteness_preservation.json。ルートimportと生成AxiomAuditは意図した更新。
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
- A-dualとExt成分の左作用・左単純商との同型は完成。Extと直和の交換、Gr(A)比較、原論文の(1.12)全体は未証明。
- 有限長双対性、区間同型のcoherence、AS条件からの周期性。WindowSystemをAS条件に加えない。
- 特定のJacobian代数についてAS分解の存在、Jacobian商とGinzburg dg代数、外部一般定理、主定理の同型類対応。

命題1.4は区間同型を仮定した貼り合わせのみ、命題5.1も未証明。
過去の稼働時間は不明。今回の実測区間・開始終了・所要時間はタスク記録参照。

前回の最終数学コミットc314180のmain Actions 37722129359はsuccess。12ファイルの最新artifactを確認。
CI検証はUTC 03:19:25.826958→03:24:43.880453、単調時計で318.053491279秒、終了0。
証拠はverification/radical_resolution_github_ci_evidence.jsonと同名のCI log。
この確認後の終了記録は文書・ログだけのコミットで、同じ数学ソースを保つ。

## 今回完成した9単位と次の実装

有限AS分解からの高次Ext消滅、全次数有限性、数値条件の逆方向、具体的左加群とExt左作用、
左Abelian構造・左単純商、Ext成分左加群の左単純商への同型、Hom/Ext⁰余極限交換、左射影性・Ext基盤、左右のA-dualとrepresentableの二重双対。
原論文との対応・仮定・利用先はdocs/as_finiteness_left_duality.md。

次は有限coproductの射影項のHomと直和の交換。全次数の自然なHom複体–Ext比較または
長完全列の自然性から、Ext(s_w,⊕P_i)の交換を導く。Gr(A)比較後に原論文(1.12)を完成扱いにできる。

9単位の差分・検査・main保存・実測時刻はRECENT_RUN.mdとruns/as-finiteness-20261008.md。
初期14モジュール・PDF・回収記録の保存確認はverification/as_finiteness_preservation.json。

今回の最終数学コミット2863bbaの[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37727782672)はsuccess。
505宣言・全223 theoremの新規監査、12ファイルの今回のartifact保存を確認。
CI検証はUTC 2026-10-08T04:30:31.595999+00:00 → 2026-10-08T04:38:32.459227+00:00、
単調時計で480.863225234秒、終了0。
証拠はverification/as_finiteness_github_ci_evidence.jsonと同名のCI log。
この確認後の最終保存は文書・記録のみ。同じ数学ソースを保ち、そのpushでもCIを新規実行する。
