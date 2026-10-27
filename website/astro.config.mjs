import { defineConfig } from "astro/config";
export default defineConfig({
    output: "static",
    site: process.env.PAGES_ORIGIN,
    base: `${(process.env.PAGES_BASE_PATH || "").replace(/\/$/, "")}/`,
});
