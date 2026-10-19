import { readdir, readFile } from "node:fs/promises";
import { zipSync, type Zippable } from "fflate";
declare const __LEAN_SOURCE_URL__: string;
export async function getProofArchive(): Promise<Uint8Array> {
    const root = new URL(__LEAN_SOURCE_URL__);
    const sources = await readdir(new URL("CliqueCertificate/", root), { recursive: true });
    const names = [
        "CliqueCertificate.lean",
        ...sources.filter(name => name.endsWith(".lean")).map(name => `CliqueCertificate/${name.replaceAll("\\", "/")}`),
        "lean-toolchain", "lake-manifest.json", "lakefile.toml",
        "README.md", ".gitignore",
    ].sort();
    const files: Zippable = Object.fromEntries(await Promise.all(names.map(async (name) => [
        `MC_vs_MC_lean/${name}`,
        [new Uint8Array(await readFile(new URL(name, root))), { mtime: new Date(1980, 0, 1), os: 0, attrs: 0 }],
    ])));
    return zipSync(files);
}
