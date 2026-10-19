import * as THREE from "three";
import type { RealPair, RealSample } from "./real-world-cache";
export function targetDisplayPose(forwardPose: THREE.Matrix4, sourceDisplayPose: THREE.Matrix4): THREE.Matrix4 {
    return sourceDisplayPose.clone().multiply(forwardPose.clone().invert());
}
export function transformScan(points: Float32Array, matrix: THREE.Matrix4): Float32Array {
    const output = new Float32Array(points.length), point = new THREE.Vector3();
    for (let i = 0; i < points.length; i += 3)
        point.fromArray(points, i).applyMatrix4(matrix).toArray(output, i);
    return output;
}
export function realDisplayFrame(pair: Pick<RealPair, "target">, sample: RealSample): THREE.Matrix4 {
    const up = sample.groundNormal ? new THREE.Vector3().fromArray(sample.groundNormal).normalize() : new THREE.Vector3(0, 0, 1);
    const rotation = new THREE.Quaternion().setFromUnitVectors(up, new THREE.Vector3(0, 0, 1));
    const frame = new THREE.Matrix4().makeRotationFromQuaternion(rotation);
    const points = transformScan(pair.target.points, frame);
    const limits = [0, 1, 2].map(axis => {
        const values = Float32Array.from({ length: points.length / 3 }, (_, i) => points[3 * i + axis]).sort();
        return [values[Math.floor((values.length - 1) * .01)] ?? 0, values[Math.ceil((values.length - 1) * .99)] ?? 0];
    });
    frame.setPosition(-(limits[0][0] + limits[0][1]) / 2, -(limits[1][0] + limits[1][1]) / 2, -limits[2][0]);
    return frame;
}
