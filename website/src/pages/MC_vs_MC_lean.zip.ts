import type { APIRoute } from "astro";
import { getProofArchive } from "../lib/proof-archive";
export const GET: APIRoute = async () => new Response(new Uint8Array(await getProofArchive()), {
    headers: {
        "Content-Type": "application/zip",
        "Content-Disposition": 'attachment; filename="MC_vs_MC_lean.zip"',
    },
});
