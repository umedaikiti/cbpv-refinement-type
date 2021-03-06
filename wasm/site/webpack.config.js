const HtmlWebpackPlugin = require('html-webpack-plugin')
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");
const MiniCssExtractPlugin = require('mini-css-extract-plugin');
const path = require('path');

module.exports = {
  entry: "./index.ts",
  resolve: {
    extensions: ['.js', '.ts', '.wasm', '.json'],
  },
  plugins: [
    new HtmlWebpackPlugin({
      template: 'index.html',
      version_info: process.env.VERSION
	}),
    new WasmPackPlugin({
      crateDirectory: path.join(__dirname, "../")
    }),
    new MiniCssExtractPlugin({
      filename: 'style.css'
    })
  ],
  module: {
    rules: [
      {
        test: /\.ts$/,
        use: 'ts-loader',
	  },
      {
        test: /\.css/,
        use: [
          MiniCssExtractPlugin.loader,
          {
            loader: 'css-loader',
            options: {
              url: false
            }
          }
        ],
      }
    ]
  }
};
