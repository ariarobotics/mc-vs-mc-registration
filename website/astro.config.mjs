import { defineConfig } from "astro/config";
export default defineConfig({
    output: "static",
    site: process.env.PAGES_ORIGIN,
    base: `${(process.env.PAGES_BASE_PATH || "").replace(/\/$/, "")}/`,
    vite: {
        define: {
            __LEAN_SOURCE_URL__: JSON.stringify(new URL("../lean/", import.meta.url).href),
        },
    },
});
