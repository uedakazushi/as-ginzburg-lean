# Codexクラウドへの引継ぎ

## 現行のB(ΦB)基礎代数回収と検証（単位214〜275）

公開132〜213は全体検証済み。本来のGinzburgRegularから元のASRegular全体、foundationへのexact制限と実際のProjectiveResolution/単純射影次元≤2/高次Ext消滅、真のI/(IJ+JI)とcategorical AS核radical商の全成分同型、最小関係基底と実際の持上げ・mod分解生成性まで完成。

214〜242の29数学モジュールは新しい全体ビルド・全宣言公理監査を含め実終了0で検証済み。元のASRegularから原論文の候補ΦB=Σ[ρrρ]を本来のPotential型で構成し、cut微分=選んだrρ、unroll後の元の表示核と最小関係商類、有限高さ差帰納法による第零sheet全表示核の実際の関係イデアル生成性を証明。225の一般補題の条件は227で元のASRegularから導出済み。有限FoundationAlgebra反対環ModuleCatへの総加群関手と冪等成分回収関手も構成済み。

WORK243〜275の33数学モジュールは個別Lean実終了0・診断なし、今回の公開659モジュール全体検査対象外。元の成分抽出とPi.singleによる線形同型/元A.Hom作用適合性から単位自然同型を構成。直交冪等射影の単位和から任意環加群の実際の有限成分和復元、全行列成分分解から全環作用適合性と余単位自然同型を証明。既存FoundationRightModuleと実際FoundationAlgebra反対環ModuleCatの圏同値、両関手のk線形性、EnoughProjectives/HasExtと全対象・全次数の実際Extのk線形保存まで完成。AS制限単純の実際環射影分解、元ASRegularから環モデルの射影次元≤2/任意標的へのExt≥3消滅まで完成。単位256〜268で元AS表示の実際有限環全射、本来の最小関係成分イデアルによる環商AlgEquiv、非cut自由道環と第零sheet自由道環の単位/積保存AlgEquiv、本来の関係イデアルを引戻した非cut環商から元foundation環の回収を証明。選んだ非cut関係と元の最小関係持上げを照合し、窓外の積零性から有限環両側イデアルの成分イデアルへの拡張も証明。必要なExt同型や正則性を仮定にしていない。 単位269〜275で有限行列成分による関係イデアルの正確な生成性を証明し、非cut自由道環と零sheet環のAlgEquivで移送した。候補ΦBのcut微分集合は選んだ最小関係集合と等しく、本来の非cut Jacobian環B(ΦB)≃ₐ元FoundationAlgebraを元ASRegularのみから証明した。追加の関係生成仮定は残っていない。全ZAlgebraの回収とΦBのGinzburgRegularは別の未証明課題である。

WORK243〜264：22数学モジュール/78異なる宣言、UTC2026-10-09T08:58:40.628910+00:00→2026-10-09T08:59:11.273619+00:00、実測30.644710692秒、監査実終了0・厳密照合成功・許容公理3種類のみ・source SHA一致。 WORK265〜275：11数学モジュール/38異なる宣言、UTC2026-10-09T09:21:14.446460+00:00→2026-10-09T09:21:49.701619+00:00、実測35.255161469秒、監査実終了0・厳密照合成功・許容公理3種類のみ・source SHA一致。

未証明：現行FoundationAlgebraのA.{u,u}からu,vへの宇宙一般化、周期整合したfinitecut基底降下、候補ΦBのGinzburgRegularと元の全ZAlgebra回収、Reyes/Hanihara/Keller接続、選択独立性/同型類対応/§5quadratic。非cut関係イデアルのcut微分による生成性と元foundation環の回収は275で完成。条件付き一般生成補題の仮定は270/273/275で元のASRegularから導出済み。候補構成やfoundation環同型を正則性/主定理完成と扱わない。定理3.2と系5.2は未証明・正式Lean定理文未実装。周期性/必要Ext表/Calabi–Yau性/主結論を新しい仮定にしない。

現行公開659数学モジュールの新しい全体run20261009T082942Z-cddaa6a5はsuccess：3831異なる宣言/2081 theorem、回帰テスト/ソース監査/固定環境/lake build/全#print axioms/照合の全6段階実終了0、wrapper0、現行公開ソースSHA完全一致。許容公理3種類のみ、重複/監査漏れ/holes/独自axiom/禁止依存なし。UTC2026-10-09T08:29:42.868298+00:00→2026-10-09T09:14:36.877841+00:00、実測2694.009537847秒。初期14・開始時60数学モジュール、577保護記録とPDF無変更の保存検査0。214〜242の29単位の検証済み差分を保存済み。main6953a852は先の630モジュールの検証済み保存先であり、659モジュールを次の通常fast-forwardで直接mainへ保存する。WORK243〜275は個別コンパイルと上記バッチ公理監査に成功、公開lake buildへの統合は次の全体検査で行う。

main6953a852のGitHub CI run37905210909は最後の取得時点でin_progress。前main5c6e119のrun37899618525は全7検査0/success、全文1,355,167bytes/SHA256b0c9a20739abffb911598b9fa361db043357aba981c45625bfc6ad9d4fc41529とartifact11604452445/digestf2f430e1ceb8603db5c42f59f0798e5b6bb543f89f68f5529112e6eb1d696737を回収済み。UTC07:33:04.593229→08:38:14.407040、実測3909.813803595秒。旧main80eee11のrun37894259808は全7検査実終了0/success、全文ログ/artifact証拠を保存済み。旧成功を新headの成功と扱わない。mainのAPI exact tree/parent/refとローカル通常fast-forward実終了0、PR/force/履歴書換えなし。

過去の単位説明は当時の状態であり、現在の判定はこの概要と該当SHAの実終了コードを使う。


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
開始時の60数学モジュールは無変更。canonical二重双対は有限生成射影・有界cochainホモトピー圏・有限次元の実際Ext³まで完成。具体的局所単位付きGr(A)圏と全次数Ext比較、総ベクトル双対の自然比較・全作用適合性、AS条件からの正負周期性、左右総正則Ext比較・全作用適合性まで完成。標準RHomの符号・shift/derived/perfectは未完成。道代数全射と(1.8)/(1.10)は単位40で完成。

## 現在の検査と保存

現行公開659数学モジュールの新しい全体run20261009T082942Z-cddaa6a5はsuccess：3831異なる宣言/2081 theorem、回帰テスト/ソース監査/固定環境/lake build/全#print axioms/照合の全6段階実終了0、wrapper0、現行公開ソースSHA完全一致。許容公理3種類のみ、重複/監査漏れ/holes/独自axiom/禁止依存なし。UTC2026-10-09T08:29:42.868298+00:00→2026-10-09T09:14:36.877841+00:00、実測2694.009537847秒。初期14・開始時60数学モジュール、577保護記録とPDF無変更の保存検査0。214〜242の29単位の検証済み差分を保存済み。main6953a852は先の630モジュールの検証済み保存先であり、659モジュールを次の通常fast-forwardで直接mainへ保存する。WORK243〜275は個別コンパイルと上記バッチ公理監査に成功、公開lake buildへの統合は次の全体検査で行う。

各単位の差分はruns/total-algebra-20261008-unit*.patch、全検査ログはverification/runs/。
初期14・開始時60数学モジュールのSHA一致と、PDF・過去577ファイル無変更はverification/total_algebra_preservation.json。
ASGinzburg.leanは新モジュールimport、AxiomAudit.leanは全明示宣言への生成更新。
過去の回収・checkpoints・実行ログは保持。

GitHub APIでローカルtree SHAとexpected_shaを照合し、force=falseで直接mainへ保存。
ローカルmainも正確なAPI commit objectへ同期。CLI pushの認証エラーが修復されたとは扱わない。
各正確なheadのCI状況はRECENT_RUN.md参照。単位1 main d9ef672のCI 37742548753はsuccess。
その全jobログ・実測645.683223858秒・全7段階0・artifact 11535012308はverification/total_algebra_unit1_github_ci*。
以前の成功は新しい数学headの成功判定に使わない。
単位44 main 62c993013d3ed1f0acead180fe4d28239406ce47のCI37837137283はsuccess・全7段階0。検証器UTC20:08:28.129649→20:45:09.006324、monotonic2200.876672221秒。完全ジョブログ/証拠はverification/total_algebra_unit44_github_ci*。この旧headの成功をlatestheadの成功として扱わない。

単位42 main 9541c0cd8866345663bf7c215a086ee12c293082のCI 37827670317は全7段階0・success。検証器のUTC18:53:08.371822→19:37:03.136589、monotonic2634.764763527秒、完全ジョブログ/証拠はverification/total_algebra_unit42_github_ci*。この旧headの成功を最新headの成功として扱わない。


```bash
AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux bash scripts/check.sh
```

初回は--prepare-cacheを追加。固定環境でpush/pull_requestごとに新規検査とartifact保存。lake updateは不要。

## 次に必要な証明義務

1. 具体的な成分復元関手と単位・余単位による左右圏同値は完成。
2. Abelian構造・EnoughProjectivesと、導来圏の同値による全次数Extのk線形同型は完成。前合成・後合成の自然性も完成。正則総加群と総代数の同定と(1.12)への移送も完成。
3. canonicalな二重A-dualの評価と自然性・representable評価同型は完成。有限生成射影の反変同値まで完成。有界cochainホモトピー圏まで完成。左単純分解とExtの相互計算も完成。二重Ext自然同型・有限次元Ext³反変同値・成分線形双対の反変同値・exactな自己同値と頂点単純の移送は完成。総ベクトル双対比較・全作用適合性とAS条件からの周期性まで完成。次は左側総正則Ext比較も完成。次はd₁からの道代数提示と標準RHom/derived接続。
4. D Ext³の区間制限・projective cover・正規化同型、代数成分回収と区間coherence、AS条件からの正負周期性は完成。道代数全射・最小生成元の基底と成分分解は完成。核の矢イデアル平方への包含と実際の道代数商同型も完成。任意の基底の持上げ・選択の独立性と最小関係を続ける。
5. 単位44で全d²=0、実際のcochain複体/homology・GinzburgRegular定義、Jacobianイデアル＝境界とH⁰の線形比較は公開検証済み。単位45で固定cut項/homologyの有限次元性と有界性、実際のretract、全正則性のcut成分判定、homogeneous Jacobian/H⁰の線形比較、道/線形unrolling同型まで公開検証済み。単位46でJacobian商とunrollingの交換・homogeneous商の積保存、固定cut H⁰とA(Φ)成分の線形比較も公開検証済み。単位47でH⁰そのものの積/単位元/結合則、Jacobian/A(Φ)比較の積保存、実際のH⁰ ZAlgebra同型、全単位的Jacobian/H⁰成分環とAlgEquivまで公開検証済み。canonical augmentation/quasi-isomorphismと実際のfree-generator augmentation complex/負次数消滅は単位48で公開検証済み。3層のprefix complex比較・homology集中・canonical augmentationは単位49で公開検証。実際のfiltration長完全列と3項homology複体のaugmentation quasi-isomorphismは単位50で公開検証。A(Φ)係数と既存射影項の評価成分比較は単位51で公開検証。augmentation H⁰/radicalと既存射影項の四項成分複体は単位52で公開検証。degree0 path作用とactual filtered/associated/prefix homology・接続写像の自然性は単位53で公開検証。次はA(Φ)積作用との係数比較から全右加群の射を作り、augmentation/radical自然性・標準微分・最小性・AS分解/Ext表へ進む。AS条件との両方向の対応・外部一般定理・主定理の同型類対応を続ける。次の未公開草稿の検査状態はRECENT_RUN.mdに記録する。

一般の全M,N・全次数の自然なHom複体–Abelian.Ext比較も未証明。直和交換には長完全列の自然性を使用した。
古いleftDerived型ProjectiveResolution.isoExtを新しいAbelian.Extの比較と取り違えない。
命題1.4のAS条件からの正負周期性は証明済み。命題5.1も含め、主定理の同型類対応は未証明。
定理3.2と系5.2は未証明で、形式的定理文も未実装。
実測開始・終了・タスク所要時間と検証所要時間はRECENT_RUN.mdを参照。未測定の過去時間は不明。

前回ext-sumsの数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この前回CIはその時点の数学ソースの検査。今回追加した数学ソースのCIは別に確認する。

単位50保存前のGitHub確認 UTC 2026-10-08T23:22:32.134685+00:00：CI48 exacthead70397c53の全7段階終了0と完全ログ/artifactを保存。最新main49/f779448のActions37856162943はin_progress、最新headのCI成功は未確定。
