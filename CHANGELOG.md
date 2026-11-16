# Changelog

[PDF Editor](https://symmr.github.io/pdf-editor/) の変更履歴。
リポジトリ: [github.com/symmr/pdf-editor](https://github.com/symmr/pdf-editor/)
画面下部のバージョン表示は `docs/version.json` を参照。

形式は [Keep a Changelog](https://keepachangelog.com/ja/1.1.0/) に準拠。

## [Unreleased]

## [1.2.0] - 2026-11-16

### Added

- テキストに下線（ツールバーの U ボタン）。画面にも保存した PDF にも反映される

## [1.1.0] - 2026-11-16

### Added

- 「選択」で PDF の元の文字をクリックすると、移動・幅の変更・書式の変更ができ、ダブルクリックで書き換えられる
- フッターに「他サービス：」と各サービスへのリンク。一覧は `docs/apps.json`

### Changed

- 「文字を編集」ボタンと E キーを外した（「選択」に統合）
- ファイル選択を「ファイルを選択」と `.pdf` の2行に変更
- ヘッダーをタイトル、リード、サーバ非送信の3行に変更
- 選んだファイルを `名前 · KB` で表示

## [1.0.0] - 2026-10-29

### Added

- ブラウザ内での文字の書き換え、文字の追加、矩形塗り、ハイライト、枠線、手書き、画像の挿入
- ページの回転・削除・並べ替え・結合
- インストール済みフォントと元の色・揃えの維持
