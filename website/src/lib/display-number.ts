export function normalizeDisplayNumber(value: number): number {
    return Math.abs(value) <= 1e-12 ? 0 : value;
}
export function formatDisplayNumber(value: number): string {
    const normalized = normalizeDisplayNumber(value);
    if (normalized === 0)
        return "0";
    if (Math.abs(normalized) < .01)
        return normalized.toExponential(2);
    return String(Math.round((normalized + Number.EPSILON) * 100) / 100);
}
