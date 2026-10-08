# 現在までに完成したAS側の基盤

実際の最後の生成元による3層filtration/subcomplexesとsigned微分閉性、隣接商のactual associated-graded complexを構成。実際の道の係数とLeibnizから全有限shifted-prefix complexとのcochain同型を証明し、GinzburgRegularから各層のhomologyが生成元次数だけに集中することを導いた。canonicalな層augmentationからその実際のhomologyのsingle complexへのquasi-isomorphismまで完成。生成元次数のhomologyとA(Φ)成分の比較、有限filtrationの長完全列から標準単純分解のexactness・Ext表/AS対応を導く部分は未証明。定理3.2・系5.2は未証明で正式Lean定理文も未実装。
最新ローカル検証 20261008T221936Z-0be3dec5：329数学モジュール・2625異なる宣言・1337 theorem、全段階終了0。
単位1〜49の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/total-algebra-20261008.md。

2026年10月8日。既存の線形RightModuleを保ち、有限AS分解だけから全次数のExt(s_w,P_i)の有限性と次数4以上の消滅を証明しました。
有限AS分解の存在の下で、元のASRegularと式(1.11)の数値条件の両方向の同値が証明済みです。
具体的な左加群・A-dual・左単純商を構成し、実際のExt(s_w,P_i,p)の成分左加群が
p≠3で零、p=3でs^left_(tau^{-1}w)に同型であることを左作用ごと証明しました。
Hom(P_i,-)・Ext⁰(P_i,-)の余極限交換、左側の射影性・EnoughProjectives・実際のExtの存在も完成しました。
左A-dualも構成し、左右のrepresentableが二重A-dualで元に戻る同型を証明しました。
既存モデルのExt(s_w,⊕P_i)への直和交換は完成。具体的局所単位付きGr(A)モデルへの圏同値・Abelian構造は完成。実際のExtのk線形同型は完成。前合成・後合成の自然性は完成。(1.12)の左加群としての移送も完成。有限次元加群の実際Ext³反変同値と成分線形双対の反変同値は完成。AS条件からの正負周期性は証明済み。主定理は未証明です。

329数学モジュール、2625異なる明示的宣言、1337 theorem、290 named instanceのビルド・公理監査は終了0。
定理3.2・系5.2は**未証明、形式的な定理文も未実装**です。
任意のAでAS分解の存在を証明したとは扱わない。具体的な局所単位付きGr(A)モデルとの左右圏同値は完成。全次数のk線形Ext同型は完成。前合成・後合成の自然性は完成。(1.12)の左加群としての移送は完成。
未解決のコンパイルエラーなし。原論文に反例・矛盾を発見したという記録なし。
最新ユーザー指示により自律的に継続し、検証済み単位を直接mainへ保存する。
旧版・入力PDF・回収記録は無変更。

# 未完了部分と、主定理を完成させるための証明義務

## 現在の障害

主定理は未完成です。数学的な反例を見つけたわけではありません。
原論文の証明には、ここで実装した組合せ・線形代数より大きなホモロジー代数の構築が必要です。
既存presheafモデル上のAS正則性は、原論文(1.6)の有限最小分解の存在と
実際のAbelian.Extの総Module.rank=1により具体的に定義しました。
GinzburgRegularは実際の全Ginzburg cochain複体の負次数homologyの零性として実装済みです。AS正則性との両方向の対応と、主定理の同型類対応を述べる正式Lean定理文は未実装です。
この欠落を任意の`Prop`で置き換えたり、主定理に等しい仮定を追加したりしていません。

Lean 4.24.0のmathlibソースには、一般のAbelian圏のExt、導来圏、projective resolutionは存在します。
したがって「LeanにExtがない」ことは障害ではありません。
既存の線形右加群圏はAbelianになり、mathlibの核・余核・ShortComplex.homologyとexactnessへ接続済みです。
射影性・EnoughProjectives・標準射影分解・実際のExtの存在も接続済みです。
有限最小分解データからmathlib ProjectiveResolutionへの変換と実際Extのk線形性は完成。
実際のsyzygy短完全列からExt³(s_(tau v),P_v)≃kと、AS条件による他の全Extの消滅まで完成。
Ext成分の左加群同型は完成。全次数の直和交換・総空間・成分左作用適合性まで完成。総代数・局所単位付き加群の圏同値・Abelian構造は完成。全次数のk線形Ext同型は完成。前合成・後合成の自然性は完成。正則総加群の同定と原論文(1.12)の左加群同型も完成しました。一般Hom複体の低次数exactnessから実際Extの0/1/2次消滅を導く接続と、次数4項の零性から高次Ext消滅は完成。自然な全次数Hom複体–Ext比較は未証明ですが、直和交換には用いていません。
取得したmathlibのファイル名検索では、AS正則性、Ginzburg dg代数、Calabi–Yau completion、
高次preprojective代数をそのまま使える専用の実装を確認できませんでした。
これは全宣言を意味論的に検索した不存在証明ではありません。

## 1. AS側の定義と最小射影分解

1〜6は完成。局所単位付きGr(A)圏同値・Ext保存、有限生成射影・有界cochainホモトピー圏と有限長双対性、AS周期性まで完成。d₁から道代数全射と(1.8)/(1.10)は完成。核の矢イデアル平方への包含も完成。次は任意の基底の持上げ・選択の独立性、最小関係と標準RHom/derived接続です。左右総正則Ext比較は単位39で完成。

1. **完成**：`ZAlgebra.RightModule`のAbelian構造、核・余核の閉性と成分同型、
   mathlibのhomologyとexactness・短完全列の成分判定。
   `rightModuleProperty`の加法性・k線形性は既存の定義のまま。
2. **完成**：任意のMについて線形Yoneda評価同型と`representable v`の射影性。
   `rightModule_epi_iff_surjective`を用いてdistinguished generatorを持ち上げる。
   representableの直和によるEnoughProjectivesも完成。任意のAについて有限・最小分解の存在は未証明。
3. **完成**：正次数の右積のspanと同定したradical、商s_v、対角1次元・他の成分零、単純性、短完全列。
4. **一般radicalの閉性・自然性と、微分の像がradicalに入るminimality・因子化判定は完成**。
   原論文(1.6)の四項の有限直和・微分・完全性・左端Mono・最小性をASResolutionとして定義済み。
   与えたASResolutionから実際のmathlib ProjectiveResolutionを構成し、augmentationのQuasiIsoを証明済み。
5. **完成**：実際の全高次Extのk作用、0次Homとの線形同型、
   (1.7)の全被覆頂点・全次数の総Module.rank条件によるASRegular定義。
   各Extの有限次元性とrank≤1もAS条件から証明済み。
   任意のAやJacobian代数でASRegularが成立することは未証明。
   命題1.3のdegree-three比較と、実際のExtのdelta型次元公式は証明済み。
   Ext成分の左作用と左単純商への同型は完成。
   一般の全次数Hom複体–Ext比較は未証明。具体的Gr(A)モデルへの全次数Extのk線形保存と自然性、長完全列による直和交換は完成。正則加群の同定と(1.12)の左作用の移送も完成。

6. **完成**：有限coproductの射影項のHomと直和の自然な交換。
   実際のExtの接続写像・次元シフトの自然性と余核表示、Homの自然な核表示、
   exactな余極限に対する核と余核の交換の閉性も完成。
   有限AS分解のsyzygyのHom交換、全次数Extのexactな余極限・小さい直和との交換、
   具体的な有限台直和への線形同型と成分包含への適合性も完成。
   全representableの直和へのExtとExt成分左加群の総空間の線形同型、
   AS条件からの次数3集中・kとの線形同型・全次数有限性も完成。
   左右の有限台総空間関手の忠実性・exactness・exactnessの反映も完成。
   直和上の実際の行列作用、積・非接続積・局所単位、Ext交換同型の全成分左作用への適合性も完成。
   ASRegularからExt³上の正次数成分の実際の後合成が零であることも証明済み。
   左右総空間の恒等成分作用が成分射影に一致し、任意の有限個の元がその有限和で同時固定されることも完成。
   具体的有限射影の冪等性・台を含む有限集合による固定と、右総空間の成分作用も証明済み。
   有限台二重直和の非単位的総代数・両側局所単位と左右総空間の全総代数作用も完成。
   単位化ModuleCatの局所単位付き対象と所属条件の証明も完成。
   射の対応と左右の忠実な総加群関手も完成。
   任意の総加群射から成分自然変換を回収し、左右関手の充満性も完成。
   任意の単位化上の加群の成分作用・恒等成分射影の冪等性・直交性も完成。
   射影像からの左右成分加群の対象復元も完成。
   成分射の復元関手と局所単位付き対象のk線形直和分解も完成。
   全単位化作用への適合性・自然性・単位・余単位と具体的成分逆関手による左右圏同値も完成。
   左右関手のk線形性と局所単位付き圏のAbelian構造・EnoughProjectives・実際のHasExtも完成。
   全M,N・全次数の実際のExtのk線形保存も完成。
   前合成・後合成の自然性も完成。
   正則総空間と総代数の線形同型、全右作用と右乗法の一致も完成。
   正則総加群の加群同型・局所単位付き右対象と成分左乗法も完成。
   全総代数の左乗法と実際のExt移送、全左作用への適合性も完成。
   Extの局所単位付き左加群と(1.12)の左単純商同型・他次数の零性も完成。
   **次の実装単位**：canonical評価同型の有限生成射影への延長と有界ホモトピー圏の反変同値まで完成。cochain次数反転・有界ホモトピー圏双対同値と左単純加群の四項射影分解、canonical二重双対から左Ext消滅は完成。左Ext³の右単純加群同型と全左単純の3次以外の零性も完成。有限次元filtration・Ext³反変同値・射影次元も完成。次は左側総正則Ext比較は完成。次はd₁からの道代数提示と標準RHomの符号・shift/derivedへの接続。
   Hom(P_i,-)・Ext⁰(P_i,-)の交換は完成済み。

標準`ProjectiveResolution`と`HasExt.{v}`はEnoughProjectivesから完成しました。
`representableExtZeroLinearEquiv`は実際のExt⁰(P_i,M)とM_iの線形同型。
高次Ext(P_i,M)の消滅は射影対象が第1引数にあるためで、Ext(s_u,P_v)のAS条件ではありません。
標準分解は無限であり得るため、(1.6)の有限四項分解を得たと扱いません。
ASRegularから分解を選ぶことは定義(i)の存在条件を使います。周期性やdelta型Ext表を追加していません。
mathlibの古いleftDerived型ExtにはProjectiveResolution.isoExtがありますが、
今回使用する新しいAbelian.Extとの比較定理ではありません。両者を取り違えません。

presheafモデルと局所単位付き総加群の左右圏同値はLocallyUnitalEquivalenceで完成しました。
原論文§1.2の成分積・右作用の向きを保持した実際の総代数と単位化上の局所単位付き部分圏を構成済み。
成分逆関手と和の余単位による左右圏同値、Abelian構造・EnoughProjectives・HasExtを証明済み。
導来圏の同値を通じて、実際の全次数Extのk線形比較と自然性を証明し、(1.12)の左加群同型へ適用済み。

`ASResolution.incomingGenerator_decomposition`により、最小分解d₁から原論文(1.10)の実際の成分分解を導いた。`indecomposables_finrank`と`indecomposableGeneratorBasis`で(1.8)の次元式と基底を証明し、`ASRegular.unrolledPathPresentation_surjective`で実際の自由道ZAlgebraからの頂点固定・積と単位元を保つ全射を構成した。
単位41で構成した全射の核の矢イデアル平方への包含(1.9)と、道代数の実際の核による商との積・単位元を保つ同型まで完成。任意の基底の持上げ・選択の独立性と最小関係は未証明であり、両主定理の完成とは扱わない。

## 2. Ext双対性から周期性

1. **完成**：有限AS分解に実際のHom(-,P_v)を適用する複体。
2. **完成**：高い頂点のHom消滅からs_(τv)の0→0→0→kを得る。
3. **完成**：syzygy短完全列・実際の線形dimension shiftからExt³≃k。
   Hom cohomologyとのdegree-three線形同型も完成。一般の自然な比較は未証明。
4. **完成**：総Cardinal rank=1から他の全Extの消滅、実際のfinrank関数の有限台とFinsupp表。
   既存presheafモデルのASRegularから(1.11)の数値的順方向まで。
   逆方向も有限AS分解だけからExtの有限性を導いて証明済み。
5. **完成**：左右A-dual、一般canonical評価と自然性、representable評価同型、有限生成射影の双対の閉性・射影性・評価同型・反変同値。
   実際の複体・鎖ホモトピー・有界性と整数次数反転に延長した有界cochain反変同値、AS分解の有界[-3,0]有限生成射影複体への持上げも完成。
   AS消滅から双対複体の低次数exactness・Ext³上端余核を証明し、AS条件から全左単純加群の四項ProjectiveResolutionと全項の有限生成射影性・次数4以上零性を構成済み。
   canonical二重双対複体から左Extの全次数での3次集中と、右加群として次数3の右単純加群同型も公開ビルド・全宣言公理監査終了0で保存済み。
   標準RHomの符号・shift/derived接続とperfectの同定は未証明。
6. **完成**：左右有限次元加群の有限台・部分/商/拡大の閉性・頂点単純filtration、全次数Ext(M,P_i)の3次集中、Ext³成分加群の有限次元性・反変短完全列とk線形関手、射影次元≤3、有限生成射影表示と拡大による有限生成射影分解の貼り合わせ・長さ3の存在、全項有限生成射影の実際の四項ProjectiveResolution・次数4以上零性まで完成。左右の全次数Extのexactな余極限・小さい直和交換と、総正則加群への実際Ext比較・全総代数作用への適合性も完成。一般四項分解の双対分解とcanonical評価から、左右全有限次元加群の二重Ext³対象同型・その自然性・二重Ext自然同型と実際Ext³の反変同値まで完成。
   **次の義務**：有限次元Abelian部分圏と成分線形双対の自然反変同値・Ext³との合成による線形exactな自己同値まで完成。総空間のベクトル双対とのcanonicalな自然比較と全総代数作用への適合性も完成。左右有限次元加群の総正則Ext比較と全総代数作用適合性まで両側とも完成。残る義務は標準RHomの符号・shift/derived/perfectへの接続。
   Extの2次/4次消滅を仮定した一般短完全列補題は、その仮定を有限次元加群ではAS条件から導いて適用済み。有限長反変同値や周期性は仮定に追加していない。
7. **完成**：成分線形双対と実際Ext³との合成、頂点単純のτ⁻¹移送、有限区間の台保存と逆関手、線形exactな区間同値、切詰めrepresentableの射影被覆・本質性・End=k。
8. **完成**：既に存在を証明した頂点単純同型を頂点ごとに一度選んで全区間で共用し、被覆同型を正規化。下端変更の実際の商射との可換性と成分移送のcoherence、単位元・積保存を証明した。構成したASRegular.nakayamaWindowSystemをWindowSystem.periodIsoへ渡し、ASRegular.negativePeriodIsoとASRegular.periodIsoにより正負周期Q.verticesを導いた。単位38の新規公開ビルド・全宣言公理監査が終了0。

**WindowSystemも周期性もAS正則性の条件に追加していない。** 標準RHomの符号・shift/derived/perfectへの接続は別の未証明義務として残る。

## 3. ポテンシャル、Jacobian代数、Ginzburg dg代数

1. **cut次数1・長さ3以上の実際のポテンシャル空間は完成**。可合成な閉路の巡回類に支持された有限多項式の部分空間と、その閉路traceのspan表示を構成した。任意の非可合成語をポテンシャルとして扱っていない。
2. **完成**：始点を固定した道のtoListの単射性と語への線形同型、巡回微分の逆向き始点・終点と実際の道を値に取る線形写像。長さ≥2・補完cut次数、cut矢の微分のcut次数0、実際のポテンシャル上の(3.8)も証明した。
3. **unrolled Jacobian商の実際の構成は完成**：通常の道のsheetへのunrolling、固定cut次数の道/線形unrolling同型とeraseの逆操作、長さfiltration保存、全sheetの実際の巡回微分が生成する二側線形イデアル、矢イデアル平方への包含と対角零性、正に有向・connected・locally finiteな商ZAlgebra、商射の全射性・核・全関係の零性を証明した。有限cut graded Jacobian商の別の構成と、商を取る操作とunrollingの比較は未証明。
4. **完成**：実際の可合成拡張道の三つの次数・合成、自由線形道代数の積/単位元/結合則とhomogeneous成分の積閉性、元の道代数と次数0部分の線形同型・積保存。
5. **全square-zeroまで完成**：原論文(1.3)の生成元微分・signed Leibniz延長、次数+1とcut/winding保存、符号作用素とd²導分則を単位43で公開検証。単位44で実際の道の頂点ごとの巡回微分の交換子恒等式、loop/全生成元/全有限道/全有限線形結合でのd²=0を公開検証した。square-zeroを追加仮定にはしていない。
6. **実際の複体とH⁰の線形比較まで完成**：整数次数のmathlib CochainComplexと成分/全homology、全有限coproductとの比較を構成した。GinzburgRegularはその実際の全負次数homologyのIsZeroと定義し、正次数homologyの常時零性と0次集中との同値も証明した。真の二側Jacobianイデアルと0次境界が等しいこと、成分H⁰とJacobian商空間の線形同型、全H⁰とそれらの有限DirectSumとの加群同型も公開検証済み。cut grading/unrolling商の比較は単位45/46で完成。H⁰そのものの積との接続と全単位的Jacobian/H⁰成分環は単位47で公開検証。特定のΦの負次数acyclicity・AS条件との両方向の対応は未証明。有限箙の全Jacobian商の単位的な環、実際の道環からの商とそのkernel判定も単位47で完成。実際のH⁰成分環とのAlgEquivと全mathlib H⁰の加群表示を明示した。
7. **固定cut複体まで完成**：単位45で拡張道の固定cut空間・複体の全項と全homologyの有限次元性、具体的な有限cohomological区間外の零性、実際の複体/homologyの包含と射影のretractを証明。有限台のcut射影和と真のcycle/boundary判定から、GinzburgRegularと全固定cut複体の負次数消滅の両方向を導いた。真のJacobianイデアルのcut射影閉性・固定cut境界との一致、固定cut H⁰とhomogeneous Jacobian商との線形同型、fixed-degree道/線形空間のunrolling/eraseの同型も公開検証済み。AS条件との同値は未証明。商とunrollingの交換は単位46で完成、H⁰そのものの積との接続は単位47で公開検証済み。
8. **商とunrollingの交換まで完成**：単位46で任意整数sheet差の道/線形同型・忘却の単射性と積保存、実際の巡回微分の持上げ/忘却、真のJacobianイデアルの同次数context spanを証明した。全sheetの関係の左右積閉性とspan延長からhomogeneous Jacobianイデアルと実際のunrolled Jacobianイデアルの一致を両方向に証明。実際のhomogeneous商≅A(Φ)のHom成分、固定cut mathlib H⁰≅A(Φ)の線形同型、homogeneous商同型の積保存まで公開検証済み。正則性やAS分解の存在は仮定していない。H⁰そのものの積の接続と有限箙の全単位的Jacobian環は単位47で公開検証済み。
9. **実際のH⁰の代数構造まで完成**：単位47でsigned Leibnizから実際の境界の左右積閉性を証明し、実際のboundary商から通常/固定cutのmathlib H⁰の積を構成した。元の道からのゼロ道単位元/結合則、H⁰–Jacobian比較と固定cut H⁰–A(Φ)比較の積/単位元保存、整数添字H⁰ ZAlgebraとA(Φ)の同型まで完成。有限成分の中間頂点sumによる全単位的道環/Jacobian環・全環商同型、実際のH⁰成分環とのAlgEquiv・全mathlib H⁰の加群表示も公開検証済み。正則性からの実際の標準双加群/単純分解とAS条件との両方向対応は未証明。
10. **canonical augmentationと実際のfree-generator complexまで完成**：単位48で一般Abelian圏のcanonical homology augmentationとquasi-isomorphismの判定を証明し、通常/固定cut/unrolled Ginzburg complexのaugmentationとGinzburgRegularの同値を導いた。非空の実際の道の最後の生成元/prefixによる自由有限和表示、実際のcohomological/cut次数移動、augmentation idealのsigned微分/左右積閉性、homogeneous mathlib augmentation complexとそのGinzburgRegularからの全負次数homology消滅まで公開検証。last-generatorの3層をprefix complexesと比較し、A(Φ)上の実際の単純分解のexactnessとExt表/AS条件を導く部分は未証明。
11. **実際の3層filtrationと全associated-graded/prefix cochain同型まで完成**：単位49で実際の最後の生成元による3層filtration/subcomplexesとsigned微分閉性、隣接商のassociated-graded complexesを構成し、実際の道の係数・生成元付加・Leibnizから全有限signed shifted-prefix complexesとのcochain同型を証明した。GinzburgRegularから各層のhomologyが生成元次数だけに集中し、その実際のhomologyへのcanonical augmentationがquasi-isomorphismとなることも公開検証。A(Φ)成分との比較、filtration長完全列からの標準単純分解のexactnessとExt表/AS対応は未証明。

Jacobian商で全巡回微分が零となることと、最小関係の基底を与えることは別の証明義務。Ginzburg正則性から最小分解やAS条件を導く部分は未証明。これを入力仮定に追加しない。

## 4. 論文§2の外部一般定理

以下を証明済みのmathlib定理に帰着するか、新たに形式化する必要があります。

| 原論文で使う結果 | 必要な形式化 |
|---|---|
| Reyes–Rogalski：(2.1)–(2.3) | generalized AS regularとgraded twisted CY、smoothness、可逆双加群、Nakayama twist |
| Hanihara：(2.4)–(2.6) | perfect/finite-dimensional商圏、tilting equivalence、Serre functor、parameter 1、2-representation infiniteness |
| Herschend–Iyama–Oppermann：(2.7)–(2.8) | inverse dualizing complex、derived tensor algebra、そのH⁰と積 |
| Keller：(2.10)、c=0 | relation-extensionのGinzburg dg代数との擬同型 |
| Ginzburg：逆向き | 負次数acyclicityから標準双加群分解の完全性と3-CY双対性 |

`Conjugation.conjugateHom_comp`は、これらを経て得たHom同定が積を保つことを検証する補題です。
tiltingやCY completionそのものの代わりではありません。

原論文の引用定理を`axiom`として置けば形式的な骨組みは短く書けますが、
それを「主結果のLean証明」とは扱いません。

## 5. 同型類の全単射と選択の独立性

上記の構築後、次を残さず証明する必要があります。

- 頂点固定の代数同型の関係と、cut gradingを保つ道代数自己同型の関係。
- 二つの対応が各関係を保ち、商に降りること。
- foundation制限、最小関係の基底・代表元の選択からの独立性。
- 代表元変更を吸収する三角的な矢の置換が可逆であること。
- 周期同型を付加データとしていないことと、その選択からの独立性。
- 両合成がそれぞれの同型類において恒等となること。

現在、これらを仮定する抽象的な全単射定理は作っていません。

## 6. del Pezzo増大度とquadratic系

`positive_recurrence_unique`はHilbert関数がEuler式を満たすことを仮定します。
exact resolutionから(4.2)を導き、del Pezzo模型の多項式増大を証明して初めて§4全体が完成します。

三角形箙のcut閉路がcubicに限られること、三重テンソル積の係数表示は証明済みです。
ASRegular triangle333からの正負3周期性は単位42で証明済み。原論文§5のquadratic最小分解(5.1)を既存ASResolution triangle333の三重coproductと同定する橋は未証明であり、命題5.1全体の完成とはまだ扱わない。AS–Ginzburg対応と選択の独立性も未証明で、系5.2の同型類対応は未完成。
同じ次数の矢の像が長さ1に限られる補題から、自己同型群が三つのGLの積であることも仕上げる必要があります。

前回ext-sumsの8単位はdocs/ext_coproduct_exchange.mdに原論文との対応・仮定・利用先を記載。
前回の60数学モジュール・636宣言・全274 theoremの検査はruns/ext-sums-20261008.mdに保持。現在の検査と保存先はRECENT_RUN.md参照。
前回9単位の記録docs/as_finiteness_left_duality.mdと歴史的検証ログは保持。

前回ext-sumsの数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この前回CIはその時点の数学ソースの検査。現在追加した数学ソースのCIとは別の証拠。
