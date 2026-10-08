# 有限AS分解から実際のExtと直和の交換へ

原論文 `docs/source.pdf` §1.2–1.3、式(1.6)–(1.12)に対応する継続記録。
既存の加法的・k線形な反変presheaf `ZAlgebra.RightModule` と、新しいderived-category型の
`CategoryTheory.Abelian.Ext` を保持した。ASRegularの定義は有限最小AS分解の存在(i)と
実際の総Cardinal rank条件(ii)のまま。周期性・窓条件・必要なExt同型を追加していない。
基盤補題が一般の体で成立しても、主定理の代数閉・標数0の仮定を除いたとは扱わない。

| 証明単位・実装 | 使用する条件と得た結果 | 利用先 |
|---|---|---|
| 1・FiniteCoproductHomColimits | finite coproductのHomを有限積に自然に同定。有限biproductにより各Homの交換から全体の交換を導く。representableとAS第1・第2項へ適用 | syzygyのHom交換 |
| 2・RightModuleExtNaturalSequence | 実際のExt前合成・接続写像・射影的中項に沿うdimension shiftの自然性。長完全列からExt(X₃,-,n+1)をExt(X₂,-,n)→Ext(X₁,-,n)の余核として表示 | Ext¹の交換、Ext²・Ext³への移行 |
| 3・HomologicalColimitClosure、RightModuleHomKernel | exactな余極限と核の交換、余核による交換の閉性。Hom(X₃,-)を自然な核として構成。異なるuniverseでも加群圏の小さい直和のexactnessを導く | 三つのsyzygy短完全列への適用 |
| 4・ASResolutionExtColimits | 有限AS分解だけから全次数Ext(s_w,-,n)のexactな余極限・小さい直和との交換。包含射との適合性、具体的な有限台直和への線形同型 | Ext(s_w,⊕P_i,n)の比較 |
| 5・ASDualityRegularCoproduct | rightRegularCoproduct=⊕P_iの成分を⊕e_i A e_jに同定。Ext(s_w,⊕P_i,n)と成分Ext左加群の総空間を比較。ASRegularから次数3集中・kとの線形同型・全次数有限性 | (1.12)のdirect-sum側 |
| 6・TotalModuleSpaces | 左右の有限台総空間関手を構成。忠実性、有限極限・余極限の保存、短完全列の保存とexactnessの反映。具体的direct sumと成分包含に適合 | Gr(A)モデルの構成 |
| 7・RegularCoproductActions | ⊕P_i上の実際の行列作用、積・非接続積・局所単位・線形性。Ext交換同型が全A.Hom成分の左作用を保つ。ASRegularからExt³上の正次数の実際の後合成が零 | 原論文の左作用との比較 |

単位4では総Ext rank条件(ii)を使っていない。次数0は自然なHomの核、次数1は自然なExtの余核、
次数2・3は自然なdimension shift、次数4以上は既存の消滅結果から零関手として扱う。
任意の余極限についてはexactnessが必要だが、小さい直和の場合はそれを加群圏から証明済み。
交換の成立をASの新しい仮定にしていない。

単一台の直和・零作用の条件付き補題の仮定は、既存ASRegularからの成分消滅と左作用の証明で満たした。
この利用先に未証明の追加仮定はない。任意のAや特定のJacobian代数でAS分解の存在を証明したとは扱わない。

## 次の具体的な証明義務

1. `⊕_(i,j) A.Hom i j` の有限台非単位的代数と、その局所単位元を束ねる。
   今回の行列作用は各成分の作用と積を比較したもの。総代数・総加群の構造の代わりにはしない。
2. 左右の総空間に総代数の作用と局所単位性を構成し、成分を取る逆関手を定義する。
   単なるModuleCat値の忠実exact関手は、代数作用を保持した圏同値ではない。
3. 原論文Gr(A)との単位・余単位を持つ圏同値と、実際のExtの保存を証明する。
   これが済むまで、今回の比較を原論文(1.12)全体の完成としない。
4. canonicalな二重A-dualの評価・自然性、有限生成射影・perfect complex、有限長双対性へ進む。
5. D Ext³の有限区間への制限・projective cover・区間同型のcoherenceから周期性を導く。
   WindowSystemをAS条件に追加しない。

一般の全M,N・全次数の自然なHom複体–Ext比較も未証明。直和交換には、その未証明比較を使わず
長完全列の自然性による証明を完成させた。Jacobian商・Ginzburg dg代数・外部一般定理も残る。
定理3.2・系5.2は未証明で、形式的な定理文も未実装。

検査・SHA保存・各単位の差分・main保存先・実測区間は `RECENT_RUN.md` と
`runs/ext-sums-20261008.md`、新規の `verification/runs/`、`verification/ext_sums_preservation.json` を参照。
