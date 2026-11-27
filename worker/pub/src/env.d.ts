interface KVNamespace {
  get(key: string, type: "arrayBuffer"): Promise<ArrayBuffer | null>;
  get(key: string, type: "stream"): Promise<ReadableStream<Uint8Array> | null>;
  put(key: string, value: ArrayBuffer | ReadableStream<Uint8Array>): Promise<void>;
  delete(key: string): Promise<void>;
}

interface D1Database {
  batch(statements: D1Statement[]): Promise<unknown[]>;
}
