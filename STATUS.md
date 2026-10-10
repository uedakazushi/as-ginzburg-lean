## ユーザー指示による停止・保存（2026-10-10）

ユーザーの「作業を中止して保存して下さい。」により形式化を停止した。検証プロセスは稼働しておらず、新しい証明修正・ビルド・公理監査は開始していない。再開はユーザーの指示を待つ。

最新の公開923数学モジュール・4821異なる宣言・2661 theoremは、run `20261010T000102Z-e3e135f8` において全6段階実終了0。925公開LeanソースのSHAが検査時のソースと完全一致し、初期14・開始時60と577保護ファイル・入力PDF・固定依存の無変更確認も終了0。全宣言の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみ。検証の実測UTC開始 `2026-10-10T00:01:02.001590+00:00`、終了 `2026-10-10T00:23:12.716902+00:00`、単調時計経過 1330.715314401 秒。wrapper実終了0・経過 1330.886908685 秒。これらは停止前に開始して完了していた検証の記録である。

原論文(2.2)の真の左R加群作用と内部次数に適合する underlined Ext³(s_i,R) ≃ 左s_i(1)、各graded頂点単純の射影次元≤3とτ頂点での射影次元=3まで、この全体検証の範囲で確認した。

後続15草稿は `verification/stopped_20261010/drafts/` に元ソースと同じSHAで保存した。12件は個別Lean終了0のみ、公理監査未実施。2件は現行ソースの個別Lean終了1、1件は未検査。これらを公開923モジュールの全体成功の対象とは扱わない。全ての成功・失敗ログ、実測時刻・終了コード・ソーススナップショットを `verification/stopped_20261010/checks/` に保持した。

未完了箇所：BalancedTensorRightFunctor の Linear.map_smul の束縛順、有限直和・retract の通常射影性、CornerFieldTotalNaturality の未検査。次は次数を忘れる関手の完全性と通常の有限AS射影分解、tensor-Hom/derived Tor比較、大域次元、Reyes–Rogalski/Hanihara/Keller、全Jacobian回収・選択独立性・系5.2。定理3.2と系5.2は未証明・正式Lean定理文未実装であり、必要な結論を公理や追加仮定にしていない。

mainの直前保存は `dfcb6b85db87d4b5095454c24108c34973a53557`。今回の差分・全体検証証拠・未完成草稿・引継ぎを `[skip ci]` 付き通常コミットで直接mainへ保存する。workflowは workflow_dispatch のみで、GitHub Actionsを起動しない。保存コミットはGit履歴で確認できる。詳細な停止状態と次の手順は `verification/stopped_20261010/stop-state.json` に記録した。

以下は当時の履歴として保持する。

2026-10-10 2026-10-10T00:00:57.732321+00:00: 実際の左乗法とExt後合成の単位元/積/両側k線形性から、全内部次数Extへの真のR→End_k表現と通常左R加群を構成。元ASのみからそのkスカラー整合性・通常R有限生成性・頂点冪等元作用、次数0の対角核の具体的冪零性からの指標同定、真の左頂点単純加群とExt³のR線形同型・単純性を証明。実際の直和挿入の像による内部次数分解と左加群の内部shiftを用い、原論文(2.2)の真の次数付き左加群同型underlined Ext³(s_i,R)≃左s_i(1)まで完成。各graded頂点単純の射影次元≤3とτ頂点の射影次元=3も証明。27数学モジュール80宣言の2分割草稿公理監査は実終了0、全80宣言厳密照合・許容3公理のみ・現行SHA一致。公開923数学モジュール/4821宣言/2661 theoremの新規全体検証を開始する。直前896構成run20261009T233101Z-7cbcabeeは全体成功・maindfcb6b8保存済みで、この923構成の全体成功とは扱わない。GitHub Actions手動のみ、通常保存[skip ci]、maindfcb6b8のActions実行件数0確認済み。大域次元の上界/Reyes twisted CY/Hanihara/Keller、候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応・系5.2は未証明。Reyes–Rogalski arXiv:1807.10249v2の命題3.18/定理3.10を一次資料で確認し、次はk^verticesの分離性・真のenveloping環とbalanced tensor/Tor比較を形式化する。定理3.2/系5.2は未証明・正式Lean定理文未実装。引用結果や必要な結論を独自公理/追加仮定にはしていない。

2026-10-09 2026-10-09T23:51:39.503441+00:00: 公開896数学モジュール/4741異なる宣言/2619 theoremの新規全体run 20261009T233101Z-7cbcabee はsuccess、回帰16件/source監査/固定環境/4251 jobsビルド/全宣言公理監査/厳密報告の全6段階実終了0。UTC 2026-10-09T23:31:01.385514+00:00 → 2026-10-09T23:50:36.286774+00:00、単調時計実測1174.901375444秒。全4741宣言の一対一照合、許容公理propext/Classical.choice/Quot.soundのみ、現行898公開LeanソースSHA完全一致、入力PDF・初期14・開始時60と577歴史的ファイル・固定依存の無変更検査0。元ASのみから、通常右乗法と整数次数を持つ本来の正則加群R、整数内部シフトの有限双積、mathlib HasShift、実際Ext^n(s_i,R(t))の(n,t)≠(3,-1)での零性/(3,-1)でのk線形同型、全内部次数underlined Extの3次以外零性/3次のk線形同型、正次数左作用の零性まで公開全体検証済み。GitHub Actionsはworkflow_dispatchのみ・通常保存[skip ci]、今回GitHubビルドを開始しない。定理3.2/系5.2は未証明・正式Lean定理文未実装。後続work草稿では実際の左乗法/Ext後合成からの真の全R表現、kスカラー整合性、通常左R加群の有限生成性、頂点冪等元の実際作用とaugmentation指標の単純加群を個別Lean0で証明した。これらは896全体runの対象外。原論文(2.2)のR線形同型と内部次数適合性、大域次元/Reyes/Hanihara/Keller、候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応を続ける。

2026-10-09 2026-10-09T23:30:57.850622+00:00: 通常の右乗法と本来の整数斉次成分を持つ正則加群R、任意整数内部シフトとその実際の有限双積、mathlib HasShiftのcoherence、実際Ext共変関手、元ASのみからExt^n(s_i,R(t))の(n,t)≠(3,-1)での零性/(3,-1)でのk線形同型、全内部次数を直和したunderlined Extの3次以外零性/3次のk線形同型、正次数斉次元の実際左乗法・Ext後合成作用の零性を19数学モジュール59宣言で統合。草稿公理監査current-cut-regular-underlined-axioms-1は実終了0、厳密59宣言照合・許容3公理のみ・現行SHA一致。公開896数学モジュール/4741宣言/2619 theoremの新規全体検証を開始する。直前877構成run20261009T225844Z-f580c06cは全体成功・mainaeec524保存済みで、この896構成の全体成功とは扱わない。GitHub Actions手動のみ、通常保存[skip ci]。原論文(2.2)の左R加群としての適合性はまだ未証明。次草稿で実際のExt後合成作用の単位元/積/線形性と環全体への表現を構成する。定理3.2/系5.2は未証明・正式Lean定理文未実装。大域次元/Reyes/Hanihara/Keller、候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応を続ける。

2026-10-09 2026-10-09T23:19:23.768432+00:00: 公開877数学モジュール/4682異なる宣言/2596 theoremの新規全体run 20261009T225844Z-f580c06c はsuccess、回帰16件/source監査/固定環境/ビルド/全宣言公理監査/厳密報告の全6段階実終了0。UTC 2026-10-09T22:58:44.099299+00:00 → 2026-10-09T23:17:50.227864+00:00、単調時計実測1146.128593790秒。全4682宣言の一対一照合、許容公理propext/Classical.choice/Quot.soundのみ、現行879公開LeanソースSHA完全一致、入力PDF・初期14・開始時60と577歴史的ファイル・固定依存の無変更検査0。元ASからの実際のgraded根基による射影分解の最小性と全項の通常R加群としての有限生成性、representableと本来の右イデアルe_iRの右作用/双方向次数対応まで公開全体検証済み。GitHub Actionsはworkflow_dispatchのみ・通常保存[skip ci]、今回GitHubビルドを開始しない。定理3.2/系5.2は未証明・正式Lean定理文未実装。後続work草稿ではRの通常右乗法/整数内部次数を持つ正則加群、任意内部シフトの有限双積、整数shift coherence、実際Extへの接続と元ASからExt^n(s_i,R(t))の(n,t)≠(3,-1)での零性・(3,-1)でのk線形同型を個別Lean0で証明した。これらは877全体runの対象外。全内部次数Extの左R作用への適合性、大域次元/Reyes/Hanihara/Keller、候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応を続ける。

2026-10-09 2026-10-09T22:58:40.297214+00:00: 実際のgraded Jacobson根基作用による最小性、元ASからの全射影分解項の通常R加群としての有限生成性、representableと実際の右イデアルe_iRの線形同型・右作用適合性・双方向次数対応を18数学モジュール48宣言で統合。草稿全件公理監査current-cut-minimal-finite-axioms-3は実終了0、厳密48宣言照合・許容3公理のみ・現行SHA一致。公開877数学モジュール/4682宣言/2596 theoremの新規全体検証を開始する。直前859構成run20261009T223339Z-21c04ec2は全体成功・main30d87bf保存済みで、この877構成の全体成功とは扱わない。GitHub Actions手動のみ、通常保存[skip ci]。定理3.2/系5.2は未証明・正式Lean定理文未実装。通常graded正則加群Rの回収/全内部次数Ext(2.2)、大域次元/Reyes/Hanihara/Keller、候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応を続ける。

2026-10-09 2026-10-09T22:57:38.296055+00:00: 公開859数学モジュール/4634異なる宣言/2560 theoremの新規全体run 20261009T223339Z-21c04ec2 はsuccess、回帰16件/source監査/固定環境/ビルド/全宣言公理監査/厳密報告の全6段階実終了0。UTC 2026-10-09T22:33:39.206460+00:00 → 2026-10-09T22:54:11.746148+00:00、単調時計実測1232.539728750秒。全4634宣言の一対一照合、許容公理propext/Classical.choice/Quot.soundのみ、現行861公開LeanソースSHA完全一致、入力PDF・初期14・開始時60と577歴史的ファイル・固定依存の無変更検査0。実際の次数付きR右加群圏との線形同値、実際Ext保存、元ASからの頂点Extと四項射影分解まで公開全体検証済み。次の18草稿48宣言は個別Lean0・厳密草稿監査0であり、この859全体runの対象外。次草稿は実際のgraded根基による最小性・各分解項の通常R加群としての有限生成性・representableと右イデアルe_iRの作用/次数を含む同定を証明している。GitHub Actionsはworkflow_dispatchのみ、通常保存は[skip ci]、今回GitHubでビルドを開始しない。定理3.2/系5.2は未証明・正式Lean定理文未実装。通常graded正則加群の同定/全内部次数Ext(2.2)、大域次元/Reyes/Hanihara/Keller、候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応を続ける。

2026-10-09 2026-10-09T22:33:16.731442+00:00: 実際のR次数付き右加群と本来の隅被覆右加群のk線形圏同値、Abelian/EnoughProjectives/実際Extの全次数線形保存、元AS条件からの全加群圏同値・頂点Ext表・長さ3の実際射影分解を43数学モジュール122宣言で統合。単純総空間の1次元性・次数集中と頂点次数成分の線形Yonedaも個別検証済み。草稿公理監査42モジュール119宣言/1モジュール3宣言は共に実終了0・厳密照合・許容3公理のみ・現行SHA一致。公開859数学モジュール/4634宣言/2560 theoremの新規全体検査を開始する。最新全体成功は816構成run20261009T214503Z-fadcda7fであり、859構成の成功とは扱わない。main52c5f00保存済み。GitHub Actionsは手動のみ・通常保存[skip ci]。主定理3.2/系5.2は未証明・正式Lean定理文未実装。graded根基とのminimality比較・通常graded正則加群の同定/全内部次数Ext(2.2)、大域次元/Reyes/Hanihara/Kellerと候補GinzburgRegular・全Jacobian回収・選択独立性/同型類対応が残る。

2026-10-09 2026-10-09T22:06:12.137003+00:00: 公開816数学モジュール/4512異なる宣言/2500 theoremの新しい全体run20261009T214503Z-fadcda7fはsuccess、全6段階0・16回帰テスト成功・全宣言公理監査厳密照合・許容公理3種類のみ・現行818ソースSHA一致。実測1020.703201623秒。実際R上の右加群・内部整数次数分解・次数適合性・k線形次数付き加群圏と被覆加群からの関手まで公開検証済み。復元関手と成分同型の次草稿は全体対象外、圏同値/Ext移送/主定理は未完成。GitHub Actionsは手動のみ・通常保存[skip ci]。

2026-10-09 2026-10-09T21:44:39.930314+00:00: native cut環R上の実際の次数付き右加群と被覆加群からのk線形関手を23数学モジュール/91宣言で証明。公開816数学モジュール/4512宣言/2500 theoremの全体検査を開始する。最新全体成功は793/4421、run20261009T210122Z-8aac049c。main7576358は保存済み、GitHub CIは手動実行のみ・通常保存[skip ci]。逆構成/圏同値/Ext移送と主定理は未完成。

# 現在の状況

## 現行793構成の全体検証成功（2026-10-09T21:21:03.169950+00:00、形式化継続中）

793数学モジュール/4421異なる宣言/2453 theorem。新規run20261009T210122Z-8aac049cはsuccess、回帰16件/source監査/固定環境/ビルド/全宣言公理監査/厳密報告の全6段階実終了0、wrapper0。UTC2026-10-09T21:01:22.027602+00:00→2026-10-09T21:18:00.374577+00:00、単調時計実測998.346993225秒。ビルドは実測62.628091351秒。全4421宣言の一対一照合、許容propext/Classical.choice/Quot.soundのみ、現行公開795 LeanファイルのSHA完全一致。入力PDF・初期14・開始時60・歴史的577保護ファイルの無変更検査も0。

ASRegularの本来の同型不変性とRの本来の隅被覆ASRegular、実際の零次数Jacobson根基、極大斉次左イデアルの共通部分として定義したgraded Jacobson根基、真の根基商R/rad_grR≃ₐ[k]k^Q.Vertexを統合した25追加数学モジュール127宣言を含む。根基商も周期性も元AS条件だけから導き、主結論や必要Ext/CY性を仮定にしていない。main cf3ad63b8e39512ab833ff2e94b0e1101f796451は前768構成を保存済み。現行793構成の証明と検証証拠を次の通常fast-forwardで直接mainへ保存する。RECENT_RUN.md追記と監査証拠の転送はユーザーの明示許可済み。

後続草稿では実際の隅被覆加群の頂点/sheet直和に各斉次行列が作用する線形写像を構成し、単位元＝恒等写像、実際の環の積と作用合成の法則を個別Lean0で証明。直和の普遍性によるR全体→ₐ[k]End_k(M_total)^opも個別Lean0。これらの草稿は793全体成功の対象外。普通の環加群の構成・次数分解・射の対応を続ける。

最終目標の定理3.2/系5.2は未証明・正式Lean定理文未実装。通常の次数付きR加群圏比較とgraded AS条件、Reyes/Hanihara/Keller導来結果、候補ΦBのGinzburgRegularと全Jacobian回収、選択独立性・同型類対応が残る。保存やチェックポイントだけで終了せず継続する。以下は当時の記録を保持する。


## AS同型不変性と実際のgraded根基商の統合（2026-10-09T21:01:21.072792+00:00、作業継続中）

現行793数学モジュール/4421異なる宣言/2453 theorem。追加25モジュール127宣言は現行草稿の公理監査current-as-radical-invariance-axioms-1で実終了0・厳密全件照合成功・許容propext/Classical.choice/Quot.soundのみ・ソースSHA一致（UTC2026-10-09T20:58:08.109420+00:00→2026-10-09T20:59:20.855470+00:00、実測72.745944775秒）。公開importへ統合したこの793構成の新規全体検査を開始する。main cf3ad63b8e39512ab833ff2e94b0e1101f796451の768構成は全体成功・保存済みであり、793構成の成功とは扱わない。

元の頂点単純/representableの実際Ext線形保存・全rank保存、positiveActionSpan一致と最小性、実際のASResolution全体の移送、ASRegularの同型不変性、元ASのみからRの本来の隅被覆ASRegularを統合。さらにR0対角写像のAlgHom・全射性、零対角核の具体的冪零性x^Q.vertices=0と本来のJacobson根基との一致を証明。Rの次数零射影と正次数イデアル、実際の極大斉次左イデアルの共通部分としてのgraded Jacobson根基を定義し、極大性の照合から対角augmentationの核との一致、本来の商R/rad_grR≃ₐ[k]k^Q.Vertexを証明した。ASRegular.cutGradedRadicalQuotientAlgEquivは元AS条件だけからこれを導き、周期性や根基商の結論を新たに仮定しない。

普通の次数付きR加群圏との比較・graded AS条件・Reyes/Hanihara/Keller導来結果、候補ΦBのGinzburgRegular・候補全Jacobian回収、選択独立性・同型類対応・系5.2は未完成。定理3.2/系5.2は未証明・正式Lean定理文未実装。必要な周期性/Ext/CY性/主結論を追加仮定にしない。全体検査中は公開ソースを固定し、数学はwork草稿で継続する。以下は当時の記録を保持する。


## 現行768構成の全体検証成功（2026-10-09T19:33:39.017053+00:00、作業継続中）

768数学モジュール/4294異なる宣言/2375 theorem。新規run20261009T191210Z-69b757bdはsuccess、回帰16件/source監査/固定環境/ビルド/全宣言公理監査/厳密報告の全6段階実終了0、wrapper0。UTC2026-10-09T19:12:10.717970+00:00→2026-10-09T19:31:49.426096+00:00、単調時計実測1178.708123491秒。全宣言の一対一照合、許容propext/Classical.choice/Quot.soundのみ、現在の公開ソースSHA完全一致。入力PDF・初期14・開始時60・歴史的577保護ファイルも無変更検査0。

実際のRの隅成分をHomとし環自身の乗算を合成とするcornerCoverZAlgebraが元Aを回収すること、元ASのみからの回収、右加群圏のk線形同値・実際Ext保存・射影分解移送・頂点representable対応を統合した21モジュール116宣言を含む。main126ca83cc1cada54758a11baf742e865f4406c3aは前747構成保存済み、現行768構成の検証済み単位を直接mainへ通常fast-forward保存する。

後続13草稿51宣言のcurrent-as-invariance-axioms-1も実終了0・厳密照合・許容3公理のみ・現行草稿SHA一致（実測44.727966705秒）。頂点単純の対応、内在的な頂点Ext表・総rank保存、実際のpositiveActionSpanの一致、三つの完全性・端の単射・augmentation・本来の最小性を含むASResolution全体の移送、ASRegularの同型不変性、元AS条件からR被覆ASRegularを証明した。草稿証拠はverification/as_invariance_20261009に保存し、768全体成功の対象には含めない。

通常のRの次数付き加群圏への比較、graded AS条件と一般導来結果Reyes/Hanihara/Keller、候補ΦBのGinzburgRegular・候補全Jacobian回収、選択独立性・同型類対応・系5.2は未完成。定理3.2と系5.2は未証明・正式Lean定理文未実装。周期性/必要なExt/Calabi–Yau性/主結論を新しい仮定にしない。次は実際のRの対角商と次数付き加群作用を構成する。保存だけで終了せず継続する。以下は当時の記録を保持する。

## 実際のR被覆と加群比較の統合（2026-10-09T19:12:09.633415+00:00、作業継続中）

現行768数学モジュール/4294異なる宣言。21追加モジュール116宣言の草稿はcurrent-corner-modules-axioms-1で全件公理監査0・厳密照合成功・許容3公理のみ・草稿SHA一致（実測68.482765559秒）。公開importへの統合後の新しい全体検証を開始する。main126ca83cc1cada54758a11baf742e865f4406c3aの747構成は全体成功・保存済みで、この768構成の検証成功とは扱わない。

全整数周期の加法整合性、整数cut成分の合成・正方向性、零原点被覆回収、実際のRの直交頂点冪等元・和=1・各隅e_jR_me_iの同定、整数次数の積保存を証明。cornerCoverZAlgebraは実際の環の部分加群をHomとし、環自身の乗算を合成に使い、元Aを回収する。ASRegular.cutCornerCoverRecoveryは元AS条件のみを用い、周期性を仮定に追加しない。実際の右加群圏のk線形同値、全次数の実際Ext保存、頂点representable同型、AS単純の射影分解移送と4次以降の項の零性も統合した。

この被覆の右加群圏と通常のRの次数付き右加群圏の比較、graded AS条件、Reyes/Hanihara/Keller接続、候補ΦBのGinzburgRegular・候補全Jacobian回収、選択独立性・同型類対応・系5.2は未完成。定理3.2・系5.2は未証明・正式Lean定理文未実装。必要な周期性/Ext表/Calabi–Yau性/主結論を追加仮定にしない。現在は頂点単純加群の対応も証明中。以下の記録は当時の状態を保持する。

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


## 形式化状況

| 論文中の位置 | Leanファイル | 実装・証明済み | 残る範囲 |
|---|---|---|---|
| §1.1、(1.1) | `CutQuiver.lean` | cut箙、被覆頂点、heightの全単射、正のwinding、pathの次数公式 | 被覆道代数をZ-代数として束ねる同定 |
| §1.1の巡回空間 | `CutPotential.lean` | 回転商の自由ベクトル空間、cut次数、唯一のcutの分割とnormal form | 閉じた可合成道の部分空間とkQ/[kQ,kQ]の同定 |
| (3.8) | `CyclicDerivative.lean` | 巡回微分の実装、回転不変性、cut復元恒等式 | Jacobianイデアルおよび商代数との接続 |
| 道代数 | `PathAlgebra.lean` | 成分の自由ベクトル空間、双線形積、単位元、結合則 | 関係イデアルとその商、unrolling |
| (1.4) | `ZAlgebra.lean` | 具体的な成分、双線形な積、局所単位元、connected・positive・finite条件 | 総代数モデルは後続単位で構成済み。特定の代数のAS条件の成立 |
| 命題1.2の道代数全射と最小生成元 | ASGenerators、ASPathPresentation、ASMinimalGenerators、ASIndecomposables、CoproductRadicals、CoproductRadicalQuotients、ASGeneratorDimensions、ASGeneratorBasis、UnrolledPathAlgebra、UnrolledPathFiniteness、UnrolledPathZAlgebra、UnrolledPathPresentationMorphism、UnrolledSingleArrows | 最小d₁からの実際のincoming係数、全体生成、自由道ZAlgebra・積/単位元保存と全射、(1.8)の次元式と基底、(1.10)の成分分解 | 核の矢イデアル平方への包含は単位41で完成。任意の基底の持上げ・最小関係・選択の独立性 |
| (1.5) | `Representables.lean` | k線形圏と右線形presheaf、YonedaのHom同型、逆向きHomの消滅、自己Homの次元1 | 局所単位付きGr(A)モデルとの圏同値は後続単位で完成。実際のExtの自然な移送 |
| §1.2の加群圏・(1.6)の基盤 | `RightModuleAbelian.lean`、`RightModuleHomology.lean` | (余)極限の閉性、Abelian構造、核・余核・homologyの成分同型、exactness・短完全列・mono/epiの成分判定 | 一般の自然なHom複体–Ext比較 |
| (1.5)の射影対象 | `RightModuleProjectives.lean`、`RightModuleEnoughProjectives.lean` | 全Mへの線形Yoneda同型、P_vの射影性、representableの直和による射影提示、EnoughProjectives | 有限生成のprojective coverと最小分解 |
| (1.5)の単純商 | `RightSubmodules.lean`、`SimpleRightModules.lean` | 右作用で閉じた部分加群、商の短完全列、P_v A_{>0}との成分同定、s_vの対角1次元・他の成分零とSimple | 単純商のGr(A)モデルへの移送と双対性の比較 |
| (1.6)–(1.7)の基盤 | `RightModuleExt.lean` | 標準projective resolutionと正次数exactness、実際のderived-category Ext、Ext⁰(P_i,M)≃+M_i、高次Ext(P_i,M)=0 | 全M,N・全次数の自然なHom複体–Ext比較 |
| 命題1.3の数値段階 | `ExtDimension.lean` | 有限台の自然数次元表の総和1と非零項1からdelta形を導く | 実際のExt移送による原論文(1.12)の左作用を含む比較 |
| 命題1.3のtop Hom計算 | `TopCohomology.lean` | 前の空間が零ならtop cokernelはそのまま、値域kなら次元1 | 一般の自然な比較（今回、命題1.3の3次は接続済み） |
| 有限区間の代数回収と商射 | TruncatedRepresentableHom、TruncatedRepresentableRestrictions、TruncatedCoverComponents | 元の全代数成分とHomの線形同型、単位元/積保存、下端変更の全射と被覆・Homへの自然性、対角被覆同型と後合成単射性 | 区間商射適合性・coherence・AS周期性は単位38で完成 |
| 有限区間の射影被覆と移送 | NakayamaInverseWindowSupport、NakayamaWindowEquivalence、TruncatedRepresentables、NormalizedProjectiveCovers、FiniteWindowProjectives、NakayamaWindowProjectives | 逆関手の台保存、線形exactな区間同値、実際の切詰めrepresentableの有限性・Yoneda・射影被覆の本質性、End=kと正規化した移送同型 | 代数成分回収・区間coherence・AS周期性も完成 |
| 有限区間と単純の移送 | RightSingleSupportIsomorphism、SimpleVectorDuality、FiniteDimensionalSimpleTranslation、FiniteDimensionalWindows、FiniteDimensionalWindowSequences、NakayamaWindowSupport | 双対の頂点単純同型、ASからNakayamaのτ⁻¹移送、有限区間Abelian構造と包含のexactness、組成列による区間台の負方向シフト | 区間同値・射影被覆・coherenceとAS周期性も完成 |
| 命題1.4のAS周期性 | WindowPeriodicity、NakayamaWindowNormalization、NakayamaWindowComponents、NakayamaWindowCoherence、PeriodInverse、ASPeriodicity | AS条件からの被覆正規化・商射適合性・成分移送のcoherence・正負の周期同型 | 標準RHom/derived/perfectは別の未完成事項 |
| 命題3.1の共役段階 | `Conjugation.lean` | 完全忠実な線形関手と対象同型から、積を保つHom線形同型を構成 | tilting、Serre functor、高次preprojectiveとの同定 |
| §4、§5の数値計算 | `Hilbert.lean` | 一般の正のlagの漸化式の一意性、quadratic Hilbert値、増大上界 | exact resolutionからのEuler式、del Pezzo模型との幾何的比較 |
| 系5.2の線形表示 | `Tensor333.lean` | 実際の三重テンソル積、係数表示、cut関係への同型、27次元、基底変更 | tensor・potential・Jacobian代数の完全な比較 |
| 系5.2の箙 | `Triangle333.lean` | 三角形箙、全矢のwinding=1、cut次数1閉路の長さ3、明示的potentialのcut恒等式 | 箙自己同型とGL(X)×GL(Y)×GL(Z)の群・商の同定 |
| (1.3)の実際の拡張道と微分 | GinzburgGrading、GinzburgPaths、GinzburgPathAlgebra、GinzburgPathWords、GinzburgDegreeZeroAlgebra、GinzburgGeneratorDifferentials、GinzburgGeneratorGradings、GinzburgPathDifferential、GinzburgSupportedProducts、GinzburgDifferentialGradings、GinzburgLeibniz、GinzburgDifferentialSign、GinzburgDegreeZeroDifferential、GinzburgSquareProducts | 実際の道の三次数と道代数、次数0部分との同型、原論文符号の生成元微分・signed線形延長とLeibniz則・次数/cut/winding保存、符号作用素とd²導分則、元/逆矢のsquare-zero | 全square-zero・実際のmathlib複体/homology・GinzburgRegular定義とH⁰の線形比較は単位44で公開検証。積保存・cut/unrolling比較・AS条件との対応は未証明 |
| 一般radical・minimality | RightModuleRadical、RightModuleMinimality、RightModuleSimpleHom | 閉性・自然性、radicalを通る因子化、Hom(-,s_i)の零微分 | 有限生成projective coverの一般理論 |
| (1.6)の具体的分解 | ASResolution、ASResolutionComplex、ASResolutionSyzygies | 有限coproductの射影性、完全最小列、mathlib ProjectiveResolution、三つの実際の短完全列 | 特定の代数について分解の存在 |
| (1.7)の具体的条件 | RightModuleExtLinear、ASRegular | 実際Extのk作用、Ext⁰の線形同型、総Cardinal rank=1、各Extの有限次元性 | 実際のExtのk線形な保存と原論文Gr(A)内のAS条件の比較 |
| 命題1.3の順方向 | ASResolutionHomComplex、ASDualityHomTerms、ASDualityHomCohomology、RightModuleExtSequence、ASDualityExt、ASDualityDimension | 実際のHom複体、線形dimension shift、実際Ext³≃k、他Ext消滅、(1.11)の数値公式と有限台 | (1.12)の移送とAS周期性は完成。一般の自然なHom–Ext比較 |
| 有限AS分解からのExt有限性・数値的同値 | ASResolutionExtBounds、RightModuleHomFinite、ASResolutionExtFinite、ASDualityEquivalence | 任意Nへの次数4以上の消滅、Ext(s_w,P_i,p)の全次数有限性、(1.7)と(1.11)の両方向 | 実際のExt保存によるGr(A)への移送 |
| 左加群・左単純商・Ext左作用 | LeftModules、LeftModuleAbelian、LeftModuleHomology、LeftSubmodules、SimpleLeftModules、RightModuleExtLeftAction、ASDualityLeftComponents | 左Abelian圏、A-dual、左radical商、Simple、Ext成分左加群の次数集中と左単純商への同型 | 総作用と圏同値は完成。実際のExt保存・自然性と原論文(1.12)への移送 |
| 余極限交換と左射影基盤 | RepresentableHomColimits、LeftModuleProjectives、LeftModuleEnoughProjectives、LeftModuleExt | Hom(P_i,-)・Ext⁰(P_i,-)の自然な交換、左線形Yoneda・射影性・EnoughProjectives・標準分解・実際Ext | 一般の二重双対・有限生成射影への拡張、Gr(A)比較 |
| 左A-dualとrepresentableの二重双対 | LeftModuleADual | 左A-dualの実際の右作用、左右のrepresentableの二重A-dualが元に同型 | 一般の評価写像の自然性、有限生成射影・perfect complexへの拡張 |
| 有限Homと自然なExt長完全列 | FiniteCoproductHomColimits、RightModuleExtNaturalSequence | 有限Homの交換、Extの接続写像・次元シフトの自然性と余核表示 | 一般の自然なHom複体–Ext比較 |
| exactな余極限と核・余核の交換 | HomologicalColimitClosure、RightModuleHomKernel | 核・余核の交換の閉性、小さい直和のexactness、Homの自然な核表示 | 特定の代数で有限AS分解の存在 |
| 全次数Extと直和の交換 | ASResolutionExtColimits | 有限AS分解だけからExt(s_w,-,n)のexactな余極限・小さい直和保存、包含射への適合性 | Gr(A)との圏同値による移送 |
| 総空間・直和上の実際の左作用 | ASDualityRegularCoproduct、TotalModuleSpaces、RegularCoproductActions | Ext(s_w,⊕P_i,n)の成分総空間比較、ASから次数3集中、左右総空間関手の忠実性とexactness、実際の行列作用・積・局所単位・Ext交換の成分左作用適合性 | 総代数と左右圏同値は完成。実際のExt保存・自然性と原論文(1.12)への移送 |
| 総代数と左右総作用 | TotalAlgebraEmbedding、TotalAlgebra、TotalAlgebraLocalUnits、TotalComponentActions、TotalAlgebraLift、TotalModuleRepresentations | 有限台の忠実正則表現、像の積の閉性、成分積と零積、冪等な共通両側局所単位、左右総空間への非単位的代数準同型 | 左右圏同値・Abelian構造は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 局所単位付き総加群 | LocallyUnitalModules | Unitization上のModuleCat対象、右には反対環、成分作用との一致、局所単位の具体的全部分圏と総加群の所属 | 左右圏同値・Abelian構造は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 左右総加群関手 | TotalModuleFunctors | 自然変換の総空間写像、成分・全総代数作用との可換性、単位化上の射、関手の忠実性 | 充満性・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 総加群関手の充満性 | TotalModuleFullness | 誘導k作用の一致、任意の総加群射から成分射と自然変換を回収、元の射の復元、左右のFull instance | 左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 任意の単位化加群の成分作用 | UnitizationComponentActions | 元のHom成分の作用、接続積と零積、恒等成分射影の冪等性・直交性 | 成分復元・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 射影像の成分加群 | UnitizationComponentModules | 成分射影像、元のHom作用による閉性、成分写像の恒等射・合成・加法・k線形性、既存LeftModule/RightModule対象の復元 | 成分復元関手・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 成分復元関手と直和分解 | UnitizationComponentFunctors、UnitizationComponentSums | 射の制限と自然変換、左右成分関手、和の写像・成分回収・単射性、局所単位条件からの全射性・k線形同型 | 単位化作用への適合性・自然性・左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| Gr(A)の局所単位付きモデルとの圏同値 | LocallyUnitalEquivalence | 全総代数作用との可換性、単位化上の和の加群同型・自然性、具体的成分逆関手・単位・余単位・左右圏同値 | Abelian構造は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |
| 局所単位付き加群圏のホモロジー基盤 | LocallyUnitalAbelian | 左右関手の加法性・k線形性、圏同値による有限積・Abelian構造・EnoughProjectives・実際のHasExt | 実際のExtのk線形保存と自然性は後続単位で完成。原論文(1.12)への移送 |
| 圏同値による実際のExt保存 | ExactEquivalenceExt、LocallyUnitalExtComparison | 複体・導来圏の同値、single complex・shiftとの適合性、全M,N・全次数の加法的・k線形な実際のExt同型 | 前合成・後合成の自然性と正則総空間の線形同定は後続単位で完成。加群同型・左乗法・原論文(1.12)への移送 |
| 正則右総空間と総代数 | RegularTotalAlgebra | 成分包含と行列元の対応、有限台二重直和とのk線形同型、成分右作用と全総代数右表現の右乗法との一致 | 単位化上の加群同型・局所単位付き右対象と成分左乗法は後続単位で完成。全左乗法と(1.12)への移送 |
| 総代数の局所単位付き正則右加群 | RegularRightModule | 単位化の右作用の具体式、局所単位付き対象、正則総加群との加群同型、左成分乗法の右加群射とその具体式 | 全左乗法と実際のExtへの(1.12)の移送 |
| 総代数への実際Extの移送 | LinearExtTransport、RegularLeftMultiplication、RegularExtComparison | 同型に沿う線形Ext後合成と共役の適合性、全左乗法の右加群射、有限AS分解からGr(A)のExtへの直和比較と全総代数の左作用への適合性 | 局所単位付き左Ext加群、(1.12)の次数3の左単純商同型と他次数零性 |
| 総空間の有限局所単位 | TotalModuleLocalUnits | 具体的有限射影の冪等性、左右の恒等成分作用との一致、任意の有限個の元の同時固定、右成分作用の包含への適合性 | 総代数と左右圏同値は後続単位で完成。実際のExt保存・前合成・後合成の自然性も後続単位で完成。(1.12)の移送 |

| 有限生成射影分解の貼り合わせ | FiniteProjectivePresentations、FiniteProjectiveExtensionClosure、ShortExactKernels、ProjectiveExtensionCovers、FiniteProjectiveResolutionLength、ASFiniteDimensionalResolutionLength | 有限生成射影表示・有限直和と拡大の閉性・snake lemmaによる核の短完全列・実際epiと核を3段繰り返す有限射影分解存在 | 四項複体は後続単位で完成。一般有限次元Mの総正則Ext比較・二重Ext自然同型 |

| 有限次元加群の四項複体とExt交換 | FourTermProjectiveResolution、FiniteProjectiveFourTermResolution、ASFiniteDimensionalProjectiveResolution、ProjectiveResolutionHomExactness、FiniteProjectiveHomColimits、FiniteProjectiveResolutionExtColimits | 全項有限生成射影の実際の四項ProjectiveResolution・次数4以上零性・Hom複体のexactness・右有限次元加群の全次数Extの余極限/直和交換 | 総正則Extへの左作用適合比較・二重Ext自然同型 |

| 総正則Extと二重Ext対象同型 | RightResolutionDuality、LeftResolutionDuality、RightResolutionExtBidual、LeftResolutionExtBidual、FiniteDimensionalExtBidual、FiniteDimensionalRegularExtComparison | 一般四項分解の双対分解・canonical二重Ext対象同型、右有限次元加群の総正則Ext比較と全左作用適合性 | 二重Ext自然同型と有限次元Ext³反変同値は後続単位で完成。左右総正則Ext比較と周期性は完成。標準RHomへの接続 |

| 二重Ext自然同型と有限次元Ext³反変同値 | ExtClassNaturality、ProjectiveResolutionSyzygyNaturality、ResolutionExtBoundaryNaturality、DualResolutionComparisonMaps、ResolutionExtBidualNaturality、FiniteDimensionalExtEquivalence | mapping coneから実際Ext接続の自然性・双対分解比較射とcanonical評価の自然性・左右二重Ext自然同型・実際Ext³反変同値 | 有限次元Abelian部分圏・成分線形双対・有限区間のcoherenceとAS周期性も完成 |

| 有限次元Abelian部分圏と線形双対 | FiniteDiagramClosureMaps、FiniteDimensionalAbelian、SmallVectorDuality、ModuleVectorDuality、FiniteDimensionalVectorDuality、FiniteDimensionalNakayama | 左右有限次元Abelian圏・有限極限/余極限の閉性・成分線形双対の自然な反変同値・Ext³との合成による線形exactな自己同値 | 総空間のベクトル双対比較・全作用適合性、頂点/有限区間の移送と射影被覆は完成。区間coherence・AS周期性は完成。左右総正則Ext比較・全作用適合性まで完成。標準RHomへの接続 |

| 左有限次元加群の総正則Ext比較 | LeftHomColimits、LeftFiniteExtColimits、LeftRegularCoproduct、LeftFiniteRegularExtComparison、LeftRegularTotalAlgebra、RegularLeftModule、LeftRegularExtComparison、RegularRightMultiplication、LeftFiniteTotalExt | 有限生成射影Hom・全次数Extの直和交換、実際の総正則局所単位付き左加群と全右乗法、全次数Extのk線形比較・全右作用適合性 | 標準RHomの符号・shift/derived/perfectへの接続 |

| 実際の道評価と積の商・代数核 | UnrolledPathIndecomposables、ZAlgebraHomomorphisms | 長さ2以上の道は積の商で零。頂点固定Homomorphismの核の左右積閉性・対角零性・成分商同型 | 全射の核の平方への包含は単位41で完成。最小関係は未証明 |

| 道代数提示の核・平方と実際の商 | UnrolledPathArrowClasses、FreeLinearKernelSupport、UnrolledPathKernelSquare、LinearIdealProducts、UnrolledPathFiltration、UnrolledPathIdeals、ASPresentationKernel、QuotientZAlgebra、ZAlgebraIsomorphisms、ASPresentationQuotient | 長さ1の類の独立性・核の長さ2以上支持性、実際の矢イデアル平方との一致、ASRegularから(1.9)、実際の商代数・商射・第一同型定理とAS代数の商同型 | 任意の基底の持上げ・最小関係・選択の独立性 |

| 閉路ポテンシャル・巡回微分とJacobian商 | ClosedPathPotentials、PathWordEmbeddings、PathCyclicDerivativeSupport、PathCyclicDerivatives、CyclicDerivativeDegrees、PathCyclicDerivativeDegrees、CyclicDerivativeCommutators、PathUnrolling、PathDegreeUnrolling、GeneratedLinearIdeals、UnrolledJacobianRelations、UnrolledComponentHeights、UnrolledJacobianAlgebra | 実際の閉路/cut1/長さ≥3ポテンシャル、道を値に取る巡回微分と長さ/次数・(3.8)/交換子恒等式、unrolled Jacobianイデアル・平方包含と実際の商ZAlgebra・関係の零性 | signed微分とLeibnizは単位43で完成。全d²=0・実際のコホモロジー/正則性定義・H⁰の線形Jacobian商比較は単位44で公開検証。積保存・graded Jacobian/unrolling比較・AS対応は未証明 |

| 全Ginzburg複体・実際のH⁰と正則性 | VertexCyclicCommutators、PathCyclicCommutators、GinzburgLoopSquare、GinzburgSquareZero、GinzburgCochainComplex、GinzburgRegularity、PathLinearIdeals、GinzburgDegreeNegOnePaths、GinzburgBoundarySpaces、GinzburgBoundaryProducts、PathJacobianIdeal、GinzburgDualContexts、GinzburgJacobianBoundaries、GinzburgHomologyZero、GinzburgTotalHomologyZero、GinzburgPositiveHomology | 全d²=0、mathlib成分/全cochain複体とhomology、有限直和比較、実際の負次数消滅によるGinzburgRegular、正次数零性、真のJacobianイデアル＝境界、成分/全H⁰のJacobian商空間との線形比較 | H⁰積保存、cut/unrolling商比較、特定Φの正則性とAS条件との両方向対応、標準双加群分解・3-CY |

| 固定cut複体とgraded H⁰比較 | GinzburgPathFiniteness、GinzburgCutCochainComplex、GinzburgCutProjections、GinzburgCutRetracts、GinzburgCutBounds、PathCutGrading、PathJacobianGrading、GinzburgCutDegreeZero、GinzburgCutHomologyFinite、GinzburgCutHomologyZero、UnrolledPathWords、PathCutUnrollingEquiv、GinzburgCycleBoundary、GinzburgCutDecomposition、GinzburgCutRegularity | 固定cut項/homologyの有限次元性と具体的有界性、実際のretractとcycle/boundary判定、全正則性と全cut負次数消滅の同値、Jacobianのhomogeneous閉性、固定cut H⁰との線形同型、unrolling/eraseの道/線形同型 | 商のunrolling交換・H⁰積保存、AS条件との対応 |

| Jacobian商とunrollingの交換 | UnrolledPathErasure、UnrolledJacobianErasure、PathCutUnrollingComparison、UnrolledErasureIdeals、UnrolledJacobianIdealErasure、PathJacobianContexts、PathCutProducts、PathJacobianHomogeneousContexts、PathQuotientProducts、PathBetweenSheets、BetweenSheetLinearEquiv、UnrolledJacobianLiftIdeal、UnrolledJacobianContexts、BetweenSheetJacobianIdeals、JacobianUnrollingQuotient、JacobianCutQuotientProducts、JacobianUnrollingProducts | 任意整数sheet差の道/線形同型と積保存、真のhomogeneous Jacobianイデアルと実際のunrolledイデアルの一致、商のunrolling交換・homogeneous商積保存、固定cut H⁰とA(Φ)成分の線形比較 | H⁰そのものの積、全単位的Jacobian環、正則性/AS対応と標準双加群分解 |

| 実際のH⁰の代数構造 | GinzburgZeroProducts、GinzburgZeroQuotientProducts、GinzburgHomologyZeroProducts、GinzburgJacobianProducts、GinzburgCutZeroProducts、GinzburgCutZeroQuotientProducts、GinzburgCutHomologyZeroProducts、GinzburgCutJacobianProducts、GinzburgCutHomologyUnits、GinzburgHomologyZAlgebra、FiniteComponentAlgebra、PathJacobianRing、FiniteComponentAlgebraEquiv、GinzburgHomologyUnits、GinzburgHomologyRing、PathJacobianRingQuotient | 微分からのboundary閉性・実際のH⁰積/単位元/結合則、Jacobian/A(Φ)比較の積保存、整数添字H⁰代数同型、全単位的環と全環商・H⁰成分環AlgEquiv、全mathlib H⁰表示 | augmentation/quasi-isomorphismは単位48で完成、標準双加群/単純分解・GinzburgRegular/AS対応は未証明 |

| 実際のaugmentationとfree-generator complex | HomologyAugmentation、GinzburgAugmentation、GinzburgCutAugmentation、GinzburgUnrolledAugmentation、GinzburgLastGenerator、GinzburgAugmentationBasis、GinzburgAugmentationIdeal、GinzburgLastGeneratorGradings、GinzburgAugmentationGradedFree、GinzburgAugmentationComplex、GinzburgAugmentationHomology、GinzburgAugmentationRegularity | canonical augmentationのquasi-isomorphismとGinzburgRegularの同値、実際の有限free-generator表示と次数移動・signed微分閉性、augmentation complexのGinzburgRegularからの負次数homology零性 | 3層のprefix complex比較、A(Φ)上の標準単純分解のexactness、Ext表/AS対応 |

| 実際の3層filtrationとprefix cochain比較 | FinsuppSupportedQuotient、GinzburgGeneratorFiltration、GinzburgGeneratorFiltrationDifferential、GinzburgGeneratorFiltrationBounds、GinzburgGeneratorLayers、GinzburgGeneratorLayerQuotients、GinzburgGeneratorFilteredComplex、GinzburgAssociatedGradedComplex、GinzburgGeneratorLayerBasis、GinzburgLastGeneratorDifferential、GinzburgGeneratorPrefixComplex、GinzburgGeneratorPrefixHomology、GinzburgGeneratorLayerCoefficients、GinzburgGeneratorLayerClasses、GinzburgGeneratorShiftAppend、GinzburgGeneratorLayerComparison、GinzburgGeneratorAppendCoefficients、GinzburgGeneratorLayerInverse、GinzburgGeneratorLayerHomology、GinzburgGeneratorLayerConcentration、GinzburgGeneratorLayerAugmentation | 実際の隣接商とfinite signed-prefix complexesのcochain同型、正則性から各層homologyの生成元次数への集中、canonical augmentationのquasi-isomorphism | A(Φ)係数比較、filtration長完全列、標準単純分解とExt表/AS対応 |

| 実際のfiltration長完全列と3項homology複体 | GinzburgGeneratorFiltrationShortExact、GinzburgGeneratorFiltrationHomologySequence、GinzburgGeneratorFilteredAugmentation、GinzburgGeneratorFiltrationSyzygy、GinzburgGeneratorUpperFiltration、GinzburgGeneratorFiltrationKernel、GinzburgGeneratorFiltrationRadical、GinzburgGeneratorFiltrationCokernel、GinzburgGeneratorPrefixTopQuotient、GinzburgGeneratorHomologyComplex | 実際の短/長完全列とkernel/cokernelの普遍性、3項homology chain complexと正則性からのaugmentation quasi-isomorphism、actual prefix top homology quotient | A(Φ)係数・射影項の同定、A線形性/標準分解微分との照合、Ext表/AS対応 |

| 実際の層homologyとAS射影項の評価成分 | GinzburgGeneratorPrefixDifferentialCoefficients、GinzburgGeneratorPrefixBoundaryFamily、JacobianOriginSheet、GinzburgGeneratorPrefixJacobian、GinzburgGeneratorIndices、GinzburgGeneratorCoefficientIndices、GinzburgProjectiveTermComponents | actual boundary pi quotientと全integer sheetのA(Φ)有限族の同型、生成元族/終点対応、実際のTerm₁/Term₂/representableの評価成分同型 | A線形性/自然性、接続写像・標準微分、augmentation H⁰/radical、単純分解/Ext表/AS対応 |

| augmentation radicalと四項成分複体 | GinzburgAugmentationHeight、RepresentableRadicalComponents、GinzburgAugmentationHeightHomology、GinzburgAugmentationRadical、GinzburgASComponentDifferentials、GinzburgASComponentExactness、GinzburgASComponentComplex | 正則性なしの実際のaugmentation H⁰/radical成分同型、射影項の成分写像とexactness、正則性から四項成分複体/単純商augmentation quasi-isomorphism | A線形性/自然性、標準微分、最小性、右加群の実際のAS分解/Ext表/AS対応 |

| 実際の道作用とfiltration/prefix homology自然性 | GinzburgFilteredLeftAction、GinzburgAssociatedLeftAction、GinzburgFiltrationLeftNaturality、GinzburgGeneratorDifferentialNaturality、GinzburgPrefixLeftAction、GinzburgPrefixComparisonNaturality、GinzburgLayerHomologyNaturality、ModuleCatCokernelHomologyNaturality、GinzburgPrefixTopNaturality、GinzburgPrefixTopHomologyNaturality、GinzburgPrefixFamilyClasses | 実際のdegree0 path chain maps/δ自然性、append比較と逆homology同型、top homology quotient自然性とclass係数 | A(Φ)積作用/全加群の射、標準微分/最小性、AS分解/Ext表/AS対応 |

| Ginzburgからの実際の有限単純射影分解 | GinzburgASProjectiveResolution、GinzburgSimpleProjectiveDimension、GinzburgSimpleFiniteProjectiveResolution、GinzburgSimpleExtColimits、GinzburgASEndpointMinimality | 本来のGinzburgRegularからactual simple ProjectiveResolution、有限生成射影全項、Ext≥4零/PD≤3、actual Ext余極限/直和交換、D₁/D₃最小性 | 他の低次数/非対角Ext零性、AS総rank=1とASRegular(ii)、actual双対左複体の比較 |

| Ginzburgからの最小AS分解と本来のExt | GinzburgASMiddleMinimality、GinzburgMinimalASResolution、GinzburgMinimalResolutionExt、OppositePotential、OppositeGinzburgGeneratorDifferential | original Φ条件からD₂最小性、本来のGinzburgRegularからASResolution(i)、actual Ext³≃k/全次数有限性/総rank≥1 | 他のExt消滅・総rank=1/ASRegular(ii)、actual dual左複体 |

| actual反対Jacobianと左右線形加群 | OppositeGinzburgCochainIso、OppositeReflectedJacobianIso、OppositeJacobianLinearEquivalence、OppositeJacobianExactness、OppositeJacobianRepresentables | native反対正則性同値、反射ZAlgebra/線形左右加群圏同値、exactness/representable比較 | native右dualと左分解の微分比較/ASRegular(ii) |

| native左単純分解とactual Hessian | GinzburgLeftSimpleProjectiveResolution、GinzburgLeftFiniteProjectiveResolution、GinzburgLeftSimpleExtBounds、PathCyclicHessian、OppositePathCyclicHessian、GinzburgDualOriginalClassFormula、GinzburgProjectiveConnectingClasses | GinzburgRegularから全左単純のfinite genuine ProjectiveResolutionとExt≥4零性、actual Hessian反転/正長さ/cut支持とnative射影D₂ class公式 | 標準基底行列、dual/左分解の微分一致と低次数/非対角Ext零性/ASRegular(ii) |

| native射影classと恒等元基底 | GinzburgLayerHomologyClasses、GinzburgDualCoefficientRepresentatives、GinzburgLoopCoefficientRepresentatives、GinzburgLoopProjectiveConnectingClasses、GinzburgPrefixFamilyUnits、GinzburgSingleGeneratorProjectiveBasis | 全native D₂/D₃代表元とclass公式、actual prefix単位・既存射影基底の一致を全体検証 | canonical右A-dualと反対分解の全微分一致、低次数/非対角Ext零性・ASRegular(ii) |

| native全射影行列とcanonical A-dual | GinzburgGeneratorJacobianEntries、GinzburgADualMatrixFormulas、GinzburgFirstProjectiveClasses、GinzburgFirstProjectiveBasis、GinzburgFirstProjectiveYoneda | native D₁/D₂/D₃のactual Yoneda行列とD₂/D₃のcanonical A-dual行列を全体検証 | canonical右A-dualと反対分解の全微分一致、低次数/非対角Ext零性・ASRegular(ii) |

## 主結果の状態

| 主張 | 状態 |
|---|---|
| 定理3.2：一般の型QのAS–Ginzburg対応 | 未証明。形式的な定理文も未実装 |
| 命題1.3 | 既存モデルの数値的両方向とExt成分の左単純商への同型は証明済み。全次数の直和交換と成分作用適合性は証明済み。総代数・左右総作用と具体的局所単位付きGr(A)モデルへの圏同値は完成。全次数のk線形Ext同型は完成。前合成・後合成の自然性は完成。単純加群の(1.12)の左作用を含む移送は完成。一般有限次元右MのExt(M,A)比較と全左作用への適合性も完成。左側の総正則Ext比較と全右作用適合性も完成 |
| 命題1.4：AS条件からの周期性 | 証明済み。ASRegular.nakayamaWindowSystemから正負の周期同型を構成。周期性を入力条件に追加していない |
| 命題5.1：三周期性 | TrianglePeriodicityでASRegular triangle333から正負3周期性は証明済み。§5のquadratic最小分解(5.1)との三重coproductの比較は未証明 |
| 系5.2：(3,3,3)型の全単射 | 未証明。形式的な定理文も未実装 |

## 条件付き結果と残る義務

ASResolutionの存在は原論文定義(i)の条件をモデル化したもの。任意のAで導いたとは扱わない。
ASRegularの条件には周期性・WindowSystem・delta型のExt表・主定理相当の結論を含めない。
数値Ext表とcoherentなWindowSystemはAS条件から導いている。幾何的な共役・tilting・CY completionへの入力を原論文から導く証明義務は残る。
標準無限分解だけから有限性を主張しない。
古いleftDerived型ExtのisoExtを新しいAbelian.Extの比較定理と取り違えない。

- Gr(A)モデルとの左右圏同値とAbelian構造は完成。実際のExt保存と自然性も完成。正則加群の同定と(1.12)への移送。
- 全M,N・全次数の自然なHom複体–Abelian.Ext比較。命題1.3の3次比較は証明済み。
- A-dual・左単純商の同型、全次数Extと直和の交換、成分左作用への適合性は完成。総代数・局所単位付き加群との圏同値・Abelian構造は完成。実際の全次数Ext保存と自然性も完成。正則加群の同定と全左作用を保つ実際のExt移送は完成。(1.12)の左加群の束ねと次数3の同型が次の義務。
- 有限長Ext双対性と区間coherence、AS条件からの正負周期性は完成。左側総正則Ext比較は完成。道代数提示と標準RHom/derived/perfectへの接続を続ける。
- 特定のJacobian代数についてAS分解の存在、Jacobian商とGinzburg dg代数、外部一般定理、主定理の同型類対応。

ソースにsorry/admit/独自axiomなし。公理依存はpropext、Classical.choice、Quot.soundのみ。
sorryAx、Lean.ofReduceBool、Lean.trustCompilerへの依存なし。
新規数学ファイルに未解決のコンパイルエラー・lint警告なし。既存のlint警告は残存。
161は初期成果の件数で、宣言数の固定条件ではありません。

今回の証明単位はruns/ext-sums-20261008-unit*.patchと新規verification/runs/に保存。
前回のruns/radical-resolution-20261008-unit*.patchも保持。
今回の実測時刻・終了コード・次の義務・main保存先はruns/ext-sums-20261008.mdとRECENT_RUN.md。
初期14数学モジュール・入力PDFの旧SHA-256一致、recovery/とcheckpoints/の無変更を再確認。
今回の保存確認はverification/ext_sums_preservation.json。ルートimportと生成AxiomAuditは意図した更新。
CLI git pushの認証エラー(終了128)後、接続済みGitHub APIへ切り替えた。
ローカル検証済みtreeのSHA一致とexpected_shaを確認し、force=falseでmainを通常のfast-forward保存。
ローカルmainも同じAPI commit objectに同期。CLIの認証が修復されたという主張はしない。
新規PRなし。mainへのpush・最新Actionsとartifactの確認はRECENT_RUN.md参照。

ユーザーは形式化の自律的継続を明示的に指示。通常の補題について再開確認は不要。

以前のradical-resolutionタスクの最終数学コミットc314180のmain CI 37722129359はsuccess、12ファイルの当該実行artifact保存済み。
CI実行の時刻と終了0はverification/radical_resolution_github_ci_evidence.json・CI logに保存。

前回ext-sums時の優先課題だった総代数・左右圏同値と自然な全次数Ext保存は完成。現在は正則右加群の同定と(1.12)への移送を進める。
今回8単位の対応・仮定・利用先はdocs/ext_coproduct_exchange.md。
差分・検査・実測時刻・main保存先はRECENT_RUN.mdとruns/ext-sums-20261008.md。
初期14モジュール、開始時51モジュール、PDFと歴史的な487ファイルの保存確認はverification/ext_sums_preservation.json。
前回の数値的同値・左双対の証拠はverification/as_finiteness_github_ci_evidence.jsonと同名のCI logに保持。
今回の正確な数学headのCI・artifact成功を確認済み。RECENT_RUN.mdとverification/ext_sums_github_ci_evidence.json参照。

前回ext-sumsの数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この確認後の終了記録の保存は文書・ログのみ。同じ数学ソースを保持し、そのpushも新規CIを開始する。
