const path = require("path");
const HtmlWebPackPlugin = require("html-webpack-plugin");
const ExtractTextPlugin = require("extract-text-webpack-plugin");

module.exports = {
    devtool: "source-map",
    entry: "./src/index.js",
    output: {
        path: path.join(__dirname, "/dist"),
        filename: "index_bundle.js"
    },
    module: {
        rules: [{
            test: /\.(js|jsx)$/,
            exclude: /node_modules/,
            use: ["babel-loader", "eslint-loader"]
        }, {
            test: /\.css$/,
            use: ExtractTextPlugin.extract({
                fallback: "style-loader",
                use: ["css-loader"]
            })
        },
        {
            test: /\.(png|jpg|gif)$/,
            use: [{
                loader: "file-loader"
            }]
        }
        ]
    },
    devServer: {
        inline: true,
        port: 8001,
        contentBase: "./build",
        historyApiFallback: true,
    },
    plugins: [
        new HtmlWebPackPlugin({
            hash: true,
            filename: "index.html",  //target html
            template: "./src/index.html" //source html
        })
    ]
};