import { readFileSync } from "node:fs";
import { validateRecent } from "./sec2check.mjs";
const feed = JSON.parse(readFileSync("./r2.json", "utf8"));
try {
  const out = validateRecent(feed);
  console.log("VALIDATOR PASSES. entries returned:", out.entries.length);
  const ours = out.entries.filter(e => e.title === "teal-sea/zeta-lab").map(e => e.id);
  console.log("our entries present in validated output:", ours.join(", "));
} catch (e) {
  console.log("VALIDATOR STILL THROWS:", e.message);
}
