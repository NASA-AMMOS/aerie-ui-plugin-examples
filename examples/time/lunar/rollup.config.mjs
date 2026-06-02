// rollup.config.js
/**
 * @type {import('rollup').RollupOptions}
 */
import typescript from "@rollup/plugin-typescript";

export default {
  input: "./time-plugin.ts",
  output: {
    dir: "./build",
    format: "esm",
  },
  plugins: [typescript({ tsconfig: "../../../tsconfig.json" })],
};
