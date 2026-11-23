fn main() {
    // Track all SQL changes, including files added to the embedded directories.
    println!("cargo:rerun-if-changed=../../migrations/public");
    println!("cargo:rerun-if-changed=../../migrations/repo");
}
