# Codexクラウドへの引継ぎ

左側の実際Extの自然な長完全列を右加群へ束ね、canonical二重双対と余核の一意性からExt³左単純≅右単純を証明しました。全左単純の他の全次数の零性も完成し、AS条件への仮定追加はありません。
次は検証済み草稿の左右有限次元加群の頂点単純filtration・Ext集中・Ext³の反変短完全列と有限次元性・k線形反変関手・射影次元≤3を公開検査し、有限生成射影分解と二重Extの自然同型へ接続します。
標準RHomの符号・shift/derived/perfect、有限長反変同値と周期性、命題5.1と両主定理は未完成。定理3.2と系5.2の正式なLean定理文も未実装です。
最新ローカル検証 20261008T121323Z-4f5b6405：108数学モジュール・1154異なる宣言・494 theorem、全段階終了0。
単位1〜27の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/total-algebra-20261008.md。

## 場所・固定環境・権限

- リポジトリ：https://github.com/uedakazushi/as-ginzburg-lean 。作業場所：`/workspace/as-ginzburg-lean`。
- mainへ直接保存。最新ユーザー指示は自律的な継続・検証済み単位の直接push。新規PRなし、force pushなし。
- 今回の開始main：e2aa1fe65b295ec74457c3c4d09015c9d1aff473。各単位の保存SHAはRECENT_RUN.md参照。
- Lean：leanprover/lean4:v4.24.0。mathlib：f897ebcf72cd16f89ab4577d0c826cd14afaafc7。manifest全依存固定。
- 既存の加法的・k線形反変presheafのRightModule定義を保持。
- ASRegularは原論文の有限最小分解の存在(i)と実際の総Ext rank条件(ii)。周期性・WindowSystem・必要なExt同型を追加しない。
- 基盤補題が一般の体で成立しても、主定理の代数閉・標数0の仮定を弱めたとは扱わない。

## 完成した基盤と今回の継続

既存の右・左Abelian圏、成分exactness、Yoneda・EnoughProjectives、radicalと単純商、
minimality、有限ASResolutionのmathlib ProjectiveResolutionへの変換、実際のAbelian.Ext、
全次数有限性・高次消滅・数値的AS双対性の両方向を保持。
具体的Ext成分左加群の次数集中と左単純商との同型、左右A-dualとrepresentableの二重双対も完成。
前回のExt直和交換と成分作用への適合性はdocs/ext_coproduct_exchange.mdとruns/ext-sums-20261008.md。
今回の総代数・両側局所単位・左右総作用はdocs/total_algebra_comparison.md。
開始時の60数学モジュールは無変更。具体的Gr(A)比較とExt保存、有限生成射影と有界cochainホモトピー圏のcanonical双対同値、全左単純の四項射影分解と実際Extの3次集中、Ext³左単純≅右単純は完成。標準RHom・derived/perfect接続、有限長反変同値と周期性は未完成。

## 現在の検査と保存

最新ローカル検証 `20261008T121323Z-4f5b6405`、全段階終了0、690.460984100秒。
UTC 2026-10-08T12:13:23.135324+00:00 → 2026-10-08T12:24:53.596316+00:00。
JST 2026-10-08T21:13:23.135324+09:00 → 2026-10-08T21:24:53.596316+09:00。
108数学モジュール・1154異なる明示的宣言・全494 theorem・187 named instanceを監査。11回帰テスト、ソース監査、固定環境、lake build、全#print axioms、照合は終了0。
許容公理はpropext、Classical.choice、Quot.soundのみ。
sorry/admit/独自axiom、sorryAx、Lean.ofReduceBool、Lean.trustCompilerなし。
新規数学ソースの未解決コンパイルエラー・lint警告なし。旧PathAlgebraの既存lint警告は保持。
未公開の次の実装草稿の状態はRECENT_RUN.mdとタスク記録に明記する。
初期161は固定件数ではない。

各単位の差分はruns/total-algebra-20261008-unit*.patch、全検査ログはverification/runs/。
初期14・開始時60数学モジュールのSHA一致と、PDF・過去577ファイル無変更はverification/total_algebra_preservation.json。
ASGinzburg.leanは新モジュールimport、AxiomAudit.leanは全明示宣言への生成更新。
過去の回収・checkpoints・実行ログは保持。

GitHub APIでローカルtree SHAとexpected_shaを照合し、force=falseで直接mainへ保存。
ローカルmainも正確なAPI commit objectへ同期。CLI pushの認証エラーが修復されたとは扱わない。
各正確なheadのCI状況はRECENT_RUN.md参照。単位1 main d9ef672のCI 37742548753はsuccess。
その全jobログ・実測645.683223858秒・全7段階0・artifact 11535012308はverification/total_algebra_unit1_github_ci*。
以前の成功は新しい数学headの成功判定に使わない。

```bash
AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux bash scripts/check.sh
```

初回は--prepare-cacheを追加。固定環境でpush/pull_requestごとに新規検査とartifact保存。lake updateは不要。

## 次に必要な証明義務

1. 具体的な成分復元関手と単位・余単位による左右圏同値は完成。
2. Abelian構造・EnoughProjectivesと、導来圏の同値による全次数Extのk線形同型は完成。前合成・後合成の自然性も完成。正則総加群と総代数の同定と(1.12)への移送も完成。
3. canonicalな二重A-dualの評価と自然性・representable評価同型は完成。有限生成射影の反変同値まで完成。有界cochainホモトピー圏まで完成。次は標準RHom/derived接続・左単純加群の分解・有限長双対性。
4. D Ext³から区間制限・projective cover・区間同型のcoherenceを構成し、AS条件から周期性を導く。
5. Jacobian商・Ginzburg dg代数・d²=0・外部一般定理・主定理の同型類対応。

一般の全M,N・全次数の自然なHom複体–Abelian.Ext比較も未証明。直和交換には長完全列の自然性を使用した。
古いleftDerived型ProjectiveResolution.isoExtを新しいAbelian.Extの比較と取り違えない。
命題1.4は区間同型を仮定した貼り合わせのみ、命題5.1も未証明。
定理3.2と系5.2は未証明で、形式的定理文も未実装。
実測開始・終了・タスク所要時間と検証所要時間はRECENT_RUN.mdを参照。未測定の過去時間は不明。

前回ext-sumsの数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この前回CIはその時点の数学ソースの検査。今回追加した数学ソースのCIは別に確認する。
