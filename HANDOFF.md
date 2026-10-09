# Codexクラウドへの引継ぎ

## 現行747構成の全体検証成功（2026-10-09T18:46:26.894697+00:00、作業継続中）

747数学モジュール/4178異なる宣言/2307 theorem。新規run20261009T182549Z-8eeec22bはsuccess。回帰16件/source監査/固定環境/全体ビルド/全宣言公理監査/厳密報告の全6段階実終了0、wrapper0。UTC 2026-10-09T18:25:49.438754+00:00→2026-10-09T18:40:52.289075+00:00、単調時計の実測902.850317739秒。全宣言を一対一照合し、許容公理propext/Classical.choice/Quot.soundのみ、公開ソースSHA完全一致。入力PDF・初期14・開始時60・歴史的577保護ファイルの無変更検査0。

実際の有限台直和k代数R、周期を使った成分の積、Rの零次数≃ₐ元FoundationAlgebra≃ₐ候補非cut Jacobian環を含む13モジュール65宣言を統合済み。一般のRはA.{u,v}、foundation環との比較はA.{u,u}。定理3.2・系5.2は未証明で正式Lean定理文未実装。候補GinzburgRegular・候補全Jacobian回収・外部導来結果・選択独立性などを引き続き証明する。必要な結論を追加仮定にしていない。

先行42モジュールと734全体成功記録はmain e718ab54f6c34021309904fce5ff3a842b4ed805へ通常fast-forward保存済み（検証済みtree 9f27aba8dfb13a5fab2a8daaafaac13a5e783f72と一致）。ユーザーはRECENT_RUN.md追記と公理監査ログ・宣言一覧など検証記録のmainへの保存を明示許可し、以前の転送拒否は解消済み。現行13モジュールと747証拠の次のmain保存を準備する。

前run20261009T175616Z-b01cb2e1は、全3 Lean監査部分0・厳密照合成功でも、combined標準出力のBroken pipeでwrapper1/axioms127となった失敗記録として保持。新規runではstdout全体をファイルへ記録し、全工程0を確認した。草稿の整数周期合成・零原点被覆から元Aの回収7モジュール35宣言はcurrent-integer-cover-axioms-1で監査0。実際のRの頂点冪等元・隅成分同定・積対応は個別Lean0で進行中。これらの草稿を747構成に含めた成功とは扱わない。次は全整数の隅成分の積対応と実際のRからの被覆回収を完成する。以下の旧記録は当時の状態を保持する。

## cut 次数付き代数の統合（2026-10-09T17:56:15.996371+00:00、作業継続中）

現行747数学モジュール/4178宣言。追加13モジュール65宣言は個別Lean実終了0・診断なし、current-cut-descent-axioms-1で全件公理監査成功（実測36.127108013秒、許容3公理のみ、草稿SHA一致）。公開importへの統合後の新規全体検証はこれから実行する。734構成のrun20261009T141039Z-350e971cは過去の当該SHAの成功であり、この新しい構成の成功とは扱わない。

原論文のAS条件から得た周期を使い、実際の非負cut成分、有限行列積、結合則・左右単位、mathlib GMonoid/GRing/GAlgebraと実際の有限台直和k代数Rを構成。各次数は有限次元。Rの零次数と元foundation環、候補の非cut Jacobian環のAlgEquivを証明。一般のR構成はA.{u,v}に対応し、既存foundation環との比較はA.{u,u}のまま。候補Jacobianの全整数周期同型も統合。全代数回収・候補GinzburgRegular・外部導来結果・選択独立性/同型類対応/系5.2は未完成。必要な結論を追加仮定にしていない。

42モジュールと734全体成功記録はlocal fb2040b7bd6c1c64e187fed4bda5db08e9925c68へ保存済み。mainは最後の確認時9ba6b363。GitHubの大きな転送を分割し小さい9treeは成功したが、RECENT_RUN.mdと大きな公理監査ログの転送が自動承認レビューに拒否され、その公開許可を非同期で質問中。未承認のデータを別手段で転送しない。形式化は継続中。以下の記録は当時の状態を保持する。


## 現行の全体検証成功（2026-10-09T14:35:39.548164+00:00、作業継続中）

公開構成は734数学モジュール/4113異なる明示的宣言/2271 theorem。新規全体run20261009T141039Z-350e971cはsuccess、回帰16件/source監査/固定環境/全体ビルド/全宣言公理監査/厳密報告の全6段階実終了0。UTC 2026-10-09T14:10:39.763026+00:00→2026-10-09T14:33:35.491459+00:00、単調時計の実測1375.728430324秒。全3監査部分も実終了0、全4113宣言の一対一照合とソースSHA完全一致、依存公理はpropext/Classical.choice/Quot.soundのみ。入力PDF・初期14・開始時60・歴史的577保護ファイルも無変更確認0。

統合42モジュールは、元AS条件からの全整数の矢整合性、全道/有限線形評価核の周期移送、全sheetのcut微分とその二側イデアルの表示核への包含、全Jacobian idealのsheet移送を含む。全整数sheetの同じsheet成分で、表示核＝本来の全Jacobian lift idealを証明し、候補Jacobian成分と元AS成分の線形同型・単位・積保存を完成。全自由道代数の整数sheet周期同型も完成。

公開統合後の草稿7モジュール18宣言では、本来の全Jacobian ideal＝erasure pullbackと候補Jacobian代数の整数周期同型、周期反復の自然数加法則、実際のcut次数付き積とその結合性・単位を個別Lean終了0・診断なしで検証。2バッチ公理監査も終了0・厳密照合成功・許容3公理のみ。これら7本は現行734の全体検査対象外で、差分と検証証拠を保存した。

定理3.2と系5.2の正式Lean定理文・証明は未完成。異なるsheetの全代数回収では、選んだ最小関係の代表元とcut矢の選択を対応させる義務が残り、既存の特定表示の全Jacobian核一致を主定理の代わりに仮定しない。候補正則性とReyes/Hanihara/Keller等の導来結果、選択独立性・同型類対応・quadraticへの接続を継続する。検証済み42モジュールを直接mainへ通常fast-forward保存する準備が整った。以下の旧記録はその時点の状態を表す。


## 現行の整数周期・同じsheetのJacobian回収（2026-10-09T14:10:22.591634+00:00、作業継続中）

WORK276〜293の復元18モジュールと新規24モジュール、計42数学モジュールを公開構成へ統合。全整数の前進周期整合性を元AS条件から導き、実際の全道と有限線形結合の評価核の周期保存を証明。候補ΦBの本来のcut微分の全sheet評価零性とその二側イデアルの表示核への包含、全Jacobian idealのsheet shift保存を完成。cut次数0の全Jacobian contextの比較から、全整数sheetの同じsheet成分について表示核＝全Jacobian lift idealを証明。その候補Jacobian成分と元AS成分の実際の線形同型と単位・積保存まで完成。自由unrolled道代数の全整数sheet周期同型も構成。原論文の仮定や必要な結論を新しい仮定にはしていない。

全42モジュールは現行依存環境で個別Lean終了0・診断なし。37/3/1/1モジュール、146/9/6/5宣言の4バッチ公理監査は全て実終了0・厳密照合成功・許容3公理のみ・当該草稿SHA一致。公開済み全宣言との重複照合を実施し、同名補題を改名して依存16モジュールを再検証した。公開importへ切り替えた734モジュールの新規全体検査は進行中で、まだ成功とは記録しない。

旧公開692構成の再検査20261009T130440Z-c3205e18は、数学モジュールのコンパイル後、build内の重複AxiomAudit実行を整理するため明示的に中断し、実終了1/failedとして保存した。初回のキャッシュ失敗2runも保持。検証器は数学ライブラリのビルド後に全宣言#print axiomsを一度実行する構成へ変更し、任意の分割実行でも各実終了コード・厳密照合・全件照合・SHAを認定条件として保持。回帰検査16件は終了0。

異なるsheet間の全Jacobian核の一致、候補GinzburgRegular、必要な外部導来結果、選択独立性・同型類対応・§5quadraticは未完成。定理3.2/系5.2は未証明・正式Lean定理文未実装。同じsheetの成分回収を全ZAlgebra回収として扱わない。全体検証後に通常fast-forwardで直接mainへ保存し、次の数学的義務を続行する。現在のmain保存済みHEADは9ba6b363aa3c2aed832c46f822263df5492170df。


## 現行のB(ΦB)回収・foundation移送表示・検証（単位214〜290）

公開132〜213は全体検証済み。本来のGinzburgRegularから元のASRegular全体、foundationへのexact制限と実際のProjectiveResolution/単純射影次元≤2/高次Ext消滅、真のI/(IJ+JI)とcategorical AS核radical商の全成分同型、最小関係基底と実際の持上げ・mod分解生成性まで完成。

214〜242の29数学モジュールは新しい全体ビルド・全宣言公理監査を含め実終了0で検証済み。元のASRegularから原論文の候補ΦB=Σ[ρrρ]を本来のPotential型で構成し、cut微分=選んだrρ、unroll後の元の表示核と最小関係商類、有限高さ差帰納法による第零sheet全表示核の実際の関係イデアル生成性を証明。225の一般補題の条件は227で元のASRegularから導出済み。有限FoundationAlgebra反対環ModuleCatへの総加群関手と冪等成分回収関手も構成済み。

243〜275の33数学モジュールは個別Lean実終了0・診断なし、2バッチの116宣言公理監査成功後に公開ソースへ統合し、692モジュールの新しい全体検査も全6段階実終了0で完了。元の成分抽出とPi.singleによる線形同型/元A.Hom作用適合性から単位自然同型を構成。直交冪等射影の単位和から任意環加群の実際の有限成分和復元、全行列成分分解から全環作用適合性と余単位自然同型を証明。既存FoundationRightModuleと実際FoundationAlgebra反対環ModuleCatの圏同値、両関手のk線形性、EnoughProjectives/HasExtと全対象・全次数の実際Extのk線形保存まで完成。AS制限単純の実際環射影分解、元ASRegularから環モデルの射影次元≤2/任意標的へのExt≥3消滅まで完成。単位256〜268で元AS表示の実際有限環全射、本来の最小関係成分イデアルによる環商AlgEquiv、非cut自由道環と第零sheet自由道環の単位/積保存AlgEquiv、本来の関係イデアルを引戻した非cut環商から元foundation環の回収を証明。選んだ非cut関係と元の最小関係持上げを照合し、窓外の積零性から有限環両側イデアルの成分イデアルへの拡張も証明。必要なExt同型や正則性を仮定にしていない。 単位269〜275で有限行列成分による関係イデアルの正確な生成性を証明し、非cut自由道環と零sheet環のAlgEquivで移送した。候補ΦBのcut微分集合は選んだ最小関係集合と等しく、本来の非cut Jacobian環B(ΦB)≃ₐ元FoundationAlgebraを元ASRegularのみから証明した。追加の関係生成仮定は残っていない。全ZAlgebraの回収とΦBのGinzburgRegularは別の未証明課題である。

WORK243〜264：22数学モジュール/78異なる宣言、UTC2026-10-09T08:58:40.628910+00:00→2026-10-09T08:59:11.273619+00:00、実測30.644710692秒、監査実終了0・厳密照合成功・許容公理3種類のみ・source SHA一致。 WORK265〜275：11数学モジュール/38異なる宣言、UTC2026-10-09T09:21:14.446460+00:00→2026-10-09T09:21:49.701619+00:00、実測35.255161469秒、監査実終了0・厳密照合成功・許容公理3種類のみ・source SHA一致。

WORK276〜290の15数学モジュールは個別Lean実終了0・診断なし。元AS条件から得た周期同型が実際の正次数積部分空間と最小生成元商を保存すること、正負任意回の周期同型とGeneratorIndex移送を証明。sheet 0のAS基底/矢代表元だけを使い、全被覆の実際の矢族、その商類＝移送基底、全自由道表示の全射性/矢イデアル平方核/真の核商≅元AS代数まで完成。元AS条件から283/285/286の具体的基底条件を284で導出済み。零sheet全道・全線形結合・整数成分/有限環表示が元AS表示に一致し、同じ非cut道表示の真の核＝候補ΦBのcut Jacobianイデアル、本来のB(ΦB)≃ₐ元FoundationAlgebraを290で証明。全Jacobian核＝この全表示核、候補正則性、任意整数反復のcoherenceは未証明。真の核商回収をA(ΦB)回収の完成として扱わない。

282のsheet添字同型が既存FoundationArrowBasisの別の同名補題と衝突することを289のimport照合で検出し、foundationSheetGeneratorIndexEquivへ改名。282/284/287/288を現行依存環境で再コンパイルして全て実終了0・診断なし。旧SHAの差分/証拠/失敗ログを無変更保存し、現行証拠へ履歴リンクを追加。草稿監査に公開済み全宣言との重複チェックを追加し、現行281〜290バッチで成功。旧281〜287バッチは旧SHAの歴史的な成功記録として保持し、現行ソースの成功判定には使わない。

WORK276〜280/26異なる宣言：UTC2026-10-09T09:46:04.264805+00:00→2026-10-09T09:46:16.622374+00:00、実測12.357572055秒、監査実終了0・厳密照合成功・許容公理3種類のみ・現行source SHA一致。 WORK281〜290/41異なる宣言：UTC2026-10-09T10:06:07.502943+00:00→2026-10-09T10:06:48.536081+00:00、実測41.033139738秒、監査実終了0・厳密照合成功・許容公理3種類のみ・現行source SHA一致。

現行692数学モジュール/3947異なる宣言/2141 theoremの新しい全体run20261009T092805Z-570508acはsuccess。全6段階実終了0、wrapper0、現行公開ソースSHA完全一致。全宣言#print axiomsを厳密照合し、許容公理propext/Classical.choice/Quot.soundのみ、重複/監査漏れ/holes/独自axiom/禁止依存なし。UTC2026-10-09T09:28:05.391088+00:00→2026-10-09T10:15:36.291672+00:00、実測2850.900579265秒。wrapper UTC09:28:05.355699→10:15:36.300343、実測2850.944647648秒。初期14/開始時60数学モジュール、577保護記録と入力PDFの無変更検査0。243〜275の33数学モジュールの全体検証済み差分を保存し、直接mainへの通常fast-forward保存を準備する。WORK276以後はこの692全体検査対象外。

WORK291〜293は個別Lean実終了0・診断なしで保存。非負sheetの実際の矢代表元の前進周期整合性、実際の周期写像と逆写像の両方向キャンセルまで完成。これらの新しいバッチ公理監査は未実行。WORK294の負sheet整合性は整数表現の依存型変換を調整中で、個別Lean失敗ログを保持し、成功とは記録していない。295の初回検査は294の未生成oleanにより終了1、未完成。零/-1境界と全整数前進整合性は未証明。

未証明：現行FoundationAlgebraのA.{u,u}からu,vへの宇宙一般化、周期整合したfinitecut基底降下、候補ΦBのGinzburgRegularと元の全ZAlgebra回収、Reyes/Hanihara/Keller接続、選択独立性/同型類対応/§5quadratic。非cut関係イデアルのcut微分による生成性と元foundation環の回収は275で完成。条件付き一般生成補題の仮定は270/273/275で元のASRegularから導出済み。候補構成やfoundation環同型を正則性/主定理完成と扱わない。定理3.2と系5.2は未証明・正式Lean定理文未実装。周期性/必要Ext表/Calabi–Yau性/主結論を新しい仮定にしない。

main0076791ff2b0d6c74c05aa2e18ef0a7b871f3467へ214〜242と659モジュール全体成功を通常fast-forward保存済み。243〜275を含む現行692モジュールの新規全体検査は完了、全6段階0。次の通常fast-forwardでこの33数学モジュールと全体検証証拠を直接mainへ保存する。保存後も形式化を継続する。

main0076791のGitHub CI run37911359000は開始済み、最後の取得時点でin_progress。前main6953a852のrun37905210909はsuccess/全7段階実終了0、全文1,382,714bytes/SHA256610d1a4ab83916023ea3151dadedc2d3d5811b0d36a21c6b0565ba9268890e8cとartifact11608860222/digestsha256:f44f260ef65eab396c6f51e024fbb3441b1e976d2a0a98c217fa83406944c8f2を回収済み。UTC2026-10-09T08:29:20.317530+00:00→2026-10-09T09:47:21.221107+00:00、実測4680.903571295秒。前main5c6e119と80eee11のCI全文/artifact証拠も保存。旧成功を新headの成功と扱わない。

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

現行692数学モジュール/3947異なる宣言/2141 theoremの新しい全体run20261009T092805Z-570508acはsuccess。全6段階実終了0、wrapper0、現行公開ソースSHA完全一致。全宣言#print axiomsを厳密照合し、許容公理propext/Classical.choice/Quot.soundのみ、重複/監査漏れ/holes/独自axiom/禁止依存なし。UTC2026-10-09T09:28:05.391088+00:00→2026-10-09T10:15:36.291672+00:00、実測2850.900579265秒。wrapper UTC09:28:05.355699→10:15:36.300343、実測2850.944647648秒。初期14/開始時60数学モジュール、577保護記録と入力PDFの無変更検査0。243〜275の33数学モジュールの全体検証済み差分を保存し、直接mainへの通常fast-forward保存を準備する。WORK276以後はこの692全体検査対象外。

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
