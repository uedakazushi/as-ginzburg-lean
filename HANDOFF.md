# Codexクラウドへの引継ぎ

2026年10月8日。既存の線形RightModuleの定義を保ち、射影性・単純加群と実際のExtへの接続を進めました。
**定理3.2・系5.2は未証明、形式的な定理文も未実装**です。

## 現在の場所と権限

- リポジトリ：https://github.com/uedakazushi/as-ginzburg-lean 。作業場所：`/workspace/as-ginzburg-lean`。
- ブランチ：`main`。最新の明示的なユーザー指示は、PRを新規作成せず、検証済み単位を直接mainへcommit・pushすること。
- 前回の検証済みAbelian・homologyブランチ`4547b79`を通常のmerge `5780346`で統合。
  以前のmainへマージしない制約は、今回のユーザー指示で置き換えられました。force pushなし。
- 通常の補題・継続方針について再度の許可確認は不要。原論文の仮定を弱めず、周期性・Ext同型・主定理相当の結論を仮定に追加しない。
- Lean：`leanprover/lean4:v4.24.0`。
- mathlib：`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。manifestの全依存を固定。

## 今回完成した証明単位

1. `RightModuleProjectives.lean`：線形Yoneda評価`(P_i ⟶ M) ≃ₗ[k] M_i`、自然性・逆写像の公式、P_iのProjective。`2e87d63`。
2. `RightModuleEnoughProjectives.lean`：全成分の全要素を添字とするrepresentableの直和からMへのepi、EnoughProjectives。`22c4b6c`。
3. `RightSubmodules.lean`：右作用で閉じた成分submoduleから線形presheaf、包含mono、商cokernel、短完全列。`dc17b2b`。
4. `SimpleRightModules.lean`：radicalと正次数の右積のspanの一致、s_iの対角1次元・他の成分零、Simple、短完全列。`86853a5`。
5. `RightModuleExt.lean`：標準projective resolutionと正次数exactness、EnoughProjectivesからHasExt、実際のExt⁰(P_i,M)≃+M_i、高次Ext(P_i,M)の消滅。`2ac9d17`。

原論文§1.2の`A_vu=e_vAe_u`・右作用`M_v×A_vu→M_u`は既存の反変関手と一致。
単純商は既存presheafモデル上で(1.5)を構成しています。
[原論文・mathlib・利用先の対応](docs/rightmodule_projective_simple_bridge.md)参照。
今回の一般の体で成立する補題は、主定理の代数閉・標数0の仮定を弱める変更ではありません。

## 実行結果と保存

最新ローカル検証 `20261008T020142Z-06538c59`：全段階終了0、61.239278秒。
UTC 2026-10-08T02:01:42.423333+00:00 → 2026-10-08T02:02:43.662622+00:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。

21数学モジュール、245異なる明示的宣言、108 theorem、37 named instanceを監査しました。
ソースにsorry/admit/独自axiomなし。標準公理propext、Classical.choice、Quot.soundのみ。
sorryAx、Lean.ofReduceBool、Lean.trustCompilerへの依存なし。
新規数学ファイルに未解決のコンパイルエラー・lint警告なし。既存のlint警告は残存。

各単位の差分は`runs/projective-simple-20261008-unit*.patch`、
時刻・終了コード・次の補題は`runs/projective-simple-20261008.md`。
新規runディレクトリにログを保存し、旧成功記録だけで判定していません。
初期14数学モジュールとPDFは旧SHA-256一致。recovery/とcheckpoints/も無変更。
ルートimport追加と生成AxiomAuditは全現行宣言への意図した更新です。
保存確認は`verification/projective_simple_preservation.json`。

## 次の検証

```bash
USE_FRO_CACHE=1 AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux \
  bash scripts/check.sh --prepare-cache
```

キャッシュがあれば`--prepare-cache`を省略。通常の再現にlake updateは不要。
CIはpush/pull_requestで固定版の同じビルド・監査を実行し、今回のログをartifactに保存します。
mainへの保存・Actionsの確認・タスク全体の実測時間はRECENT_RUN.md参照。

## 次に必要な数学的義務

- 一般のMの正次数radicalの閉性と、微分の像がradicalに入るminimality。
- (1.6)の実際の有限四項分解、完全性・最小性。標準分解の存在は有限性・長さ3を保証しません。
- 全高次Extのk作用・線形性、射影分解のHom複体とExtの比較、(1.7)のExt(s_u,P_v)の次元条件。
- presheafモデルと直和・局所単位元付きGr(A)との明示的な同値。
- AS正則性の本体、Ext双対性からの区間同型・coherence、AS条件からの周期性。
- Jacobian商、Ginzburg dg代数、外部一般定理、主定理の同型類対応。

Ext(P_i,M)の消滅をExt(s_u,P_v)の計算として扱わない。
命題1.4は区間同型を仮定した貼り合わせのみ、命題5.1も未証明。
過去の稼働時間は不明。今回の実測時間はタスク記録に保存します。

数学的コミット`2ac9d17`のmain Actionsはsuccess、12ファイルの最新artifact保存を確認。
証拠は`verification/projective_simple_github_ci_evidence.json`とRECENT_RUN.md。
