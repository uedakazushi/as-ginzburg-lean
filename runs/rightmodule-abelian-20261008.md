# RightModule Abelian構造の実装記録

目的：既存の線形右加群の定義を保ち、Abelian圏構造とmathlibのホモロジー代数に接続する。
タスク開始：2026-10-08T00:20:15+00:00（UTC時計の観測、秒精度）。
作業ブランチ：`codex/rightmodule-abelian-20261008`。mainへマージしない。
作業中。終了時刻と全所要時間は終了前に追記する。

## 単位1：極限・余極限の閉性

- 完成：`rightModuleProperty_closedUnderLimits`、`rightModuleProperty_closedUnderColimits`。
- 図式の各対象の加法性・k線形性を、射影のjoint monicity／包含射のjoint epicityと自然性から導く。
- 仮定はModuleCatに当該形状の(余)極限が存在することだけ。有限図式ではmathlibが供給する。
- 定義`RightModule`、既存14数学モジュール、PDFは変更していない。ルートimportに新モジュールを追加。
- 原論文§1.2の`A.Hom u v = e_v A e_u`の右作用`M_v → M_u`と反変関手の向きを照合。
  一般Field上の圏論的補題であり、原論文の代数閉・標数0などの主定理の仮定を変更しない。
- 検証：`20261008T002450Z-2b39e40d`、全段階終了0、28.790644秒。
  UTC 2026-10-08T00:24:50.132119+00:00 → 2026-10-08T00:25:18.922773+00:00。
  lake build、公理監査174異なる宣言／86 theorem、回帰テスト10件、固定環境、照合が成功。
- 許容公理：propext、Classical.choice、Quot.soundのみ。禁止placeholder・独自公理・禁止依存なし。
- 途中の失敗：`20261008T002426Z-5860c6e4`のbuild終了1。
  余錐のconst functorの展開を含む自然性のrewriteを修正し、解消。
- 次の利用先：full subcategoryのinclusionが(余)極限をcreateするmathlib定理。
  次の証明義務：核・余核・有限積の存在と保存、coimage-image比較の同型性、exactnessの成分判定。
- `git diff`を`runs/rightmodule-abelian-20261008-unit1.patch`へ保存する。

主定理3.2・系5.2は未証明、形式的な定理文も未実装。AS条件・Ext条件・周期性を追加仮定にしない。

## 単位2：Abelian構造と核・余核の保存

- 完成：任意の存在する形状の(余)極限のfull subcategoryへの持ち上げとcreate、有限積、
  余像→像の比較射の同型性、`rightModuleAbelian`、包含の有限(余)極限保存。
- 単位1のコミット：`2798d6f`、push終了0。
- mathlibの`ModuleCat`とambient関手圏のAbelian構造、full faithful inclusion、
  `PreservesCoimageImageComparison.iso`と`Abelian.ofCoimageImageComparisonIsIso`を使用。
- 長い宣言名でLeanの公理リストが折り返されるため、監査ログ解析を複数行に対応させた。
  重複・禁止公理・切れたリスト・未認識出力を拒否する回帰テストを追加（合計11件）。
- 検証：`20261008T002911Z-45d4d8c7`、全段階終了0、14.815409秒。
  UTC 2026-10-08T00:29:11.909605+00:00 → 2026-10-08T00:29:26.725020+00:00。
  ビルド、183異なる宣言の公理監査（86 theorem）、11回帰テスト、固定環境、照合が成功。
- 途中の失敗：`20261008T002644Z-f4e57128` build終了1（有限余極限保存の明示的introで解消）、
  `20261008T002737Z-ed8c1a7f` report終了1（公理出力の折り返し対応で解消）。
- 差分：`runs/rightmodule-abelian-20261008-unit2.patch`。
- 次の利用先と証明義務：頂点評価がホモロジーを保存すること、核・余核・homologyの成分同型、
  exactnessと線形写像の像＝核の同値、短完全列の成分判定。
