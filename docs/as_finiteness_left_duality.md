# 有限AS分解から数値的同値と左加群構造へ

原論文docs/source.pdfの§1.2–1.3、式(1.4)–(1.12)を照合した継続記録。
既存ZAlgebra.RightModuleの加法的・k線形な反変presheaf定義と、実際のAbelian.Extを保つ。
原論文の代数閉体・標数0を主定理から除いていない。基盤補題が一般の体で成立しても、主定理の仮定変更ではない。

## 有限AS分解だけから得た結果

ASResolutionは原論文(1.6)の有限最小分解そのもののデータ。
存在条件は定義1.1(i)であり、任意のAや特定のJacobian代数でその存在を証明したとは扱わない。

| 実装 | 使用する仮定と結果 | 利用先 |
|---|---|---|
| ASResolutionExtBounds | ASResolutionの三つのsyzygy短完全列、representableの射影性から、任意NへのExt(s_w,N,p)はp≥4で零 | 有限長の高次消滅、双対性 |
| RightModuleHomFinite | epiへの前合成はHomへの線形単射。有限coproductのHomは各Homの有限積。Yonedaと局所有限性から必要なHomは有限次元 | 低次Extの有限性 |
| ASResolutionExtFinite | 長完全列でExt¹はkernelのHomの商、次数2・3は次元シフト、次数4以上は消滅。全Ext(s_w,P_i,p)が有限次元 | finrankとCardinal rankの比較 |
| ASDualityEquivalence | 有限AS分解の存在の下でASRegularと式(1.11)の実際のfinrank条件が同値 | 命題1.3の数値的両方向 |

逆方向は有限性を先に証明している。無限次元のfinrank=0をrank=0と取り違えていない。
ASRegularの定義は元の分解の存在と総Cardinal rank=1のまま。
delta表は新しい仮定として定義に追加せず、この元の条件との同値を証明した。

## 左加群と左単純商

LeftModuleは同じA.Obj上の共変・加法的・k線形なModuleCat値functor。
A.Hom i j=e_j A e_iに沿い、左作用は成分iから成分jへ向かう。

- LeftModules：左表現可能加群A e_i、A-dualの成分Hom(M,P_i)、後合成による左作用。
  P_iのA-dualとA e_iの左作用を保つ同型。
- RightModuleExtLeftAction：実際のExt(M,-,p)のk線形covariant functor。
  Ext(M,P_i,p)の成分左加群。次数0でA-dualと自然に同型。
- LeftModuleAbelian・LeftModuleHomology：核・余核・homologyと、exactness・mono/epiの成分判定。
- LeftSubmodules・SimpleLeftModules：正次数の実際の左積のspanをradicalと同定し、
  A e_i/A_{>0}e_iを実際の余核商として構成。対角1次元・他の成分零・単純性・短完全列。
- ASDualityLeftComponents：ASRegularからExt(s_w,P_i,p)の左加群がp≠3で零となり、
  p=3でsimpleLeftModule(height(tau^{-1}w))に同型。正次数の作用は零。
  成分の同型はconnectedによるスカラー対角作用を使って左加群の同型へ延長する。
- RepresentableHomColimits：Hom(P_i,-)と頂点評価の自然同型から、許された全余極限shapeとの交換。
  Ext⁰(M,-)–Hom(M,-)の第2引数での自然同型と、Ext⁰(P_i,-)の余極限交換。

- LeftModuleProjectives・LeftModuleEnoughProjectives・LeftModuleExt：左線形Yonedaと射影性、
  任意左加群への実際のcoproduct射影提示、EnoughProjectives、標準分解と実際Extの存在。
  標準分解が有限であることや、左AS最小分解の存在は証明したとは扱わない。

- LeftModuleADual：左A-dualも実際のHomから右加群として構成。左右のrepresentableの
  二重A-dualは元の対象に同型。一般のcanonicalな評価とその自然性、有限生成射影への拡張は未証明。

## 省略していない残る証明義務

Ext成分左加群は具体的な数学的対象であり、任意Propによる代用品ではない。
ただし、これを原論文のExt(s_w,A)と同定するには次を証明する必要がある。

1. 原論文の局所単位元付き直和加群Gr(A)と既存presheafモデルの明示的同値、およびExt保存。
2. 有限台二重直和の非単位的総代数と、その局所単位付き左右加群の構造・逆関手。
3. 全M,N・全次数の自然なHom複体–実際のAbelian.Ext比較（直和交換には未使用）。

後続のext-sumsタスクで、有限coproductのHom交換、実際の長完全列の自然性、
有限AS分解からの全次数Ext(s_w,⊕P_i)≃⊕Ext(s_w,P_i)、全成分左作用への適合性は証明済み。
対応と残る義務は[直和交換の接続記録](ext_coproduct_exchange.md)。
総空間関手が忠実exactであることだけを、Gr(A)圏同値やExt保存の代わりにはしない。

その後に原論文の式(1.12)全体を完成扱いにできる。
有限長双対性、perfect complexの二重双対、区間同型とcoherence、AS条件からの周期性は別の未証明事項。
周期性やWindowSystemをASRegularに追加していない。tauは頂点の置換で、Aの自己同型を仮定していない。
定理3.2・系5.2は未証明、形式的な定理文も未実装。

この以前のタスクの検査・実測時刻・main保存先はruns/as-finiteness-20261008.md。現在の検証はRECENT_RUN.md参照。
