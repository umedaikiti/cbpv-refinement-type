const HtmlWebpackPlugin = require('html-webpack-plugin')
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");
const path = require('path');

module.exports = {
  entry: "./index.js",
  output: {
    path: path.resolve(__dirname, "dist"),
    filename: "index.js",
  },
  resolve: {
    extensions: ['.js', '.wasm', '.json'],
  },
  plugins: [
    new HtmlWebpackPlugin({
      template: 'index.html',
      version_info: process.env.VERSION
	}),
    new WasmPackPlugin({
      crateDirectory: path.join(__dirname, "../")
    })
  ],
  module: {
    rules: [
      {
        test: /\.css/,
        use: [
          'style-loader',
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
