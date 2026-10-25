/* SPDX-License-Identifier: MIT */
/*
 * Linux bootstrap page (data externalization for standalone AppImage / desktop).
 *
 * Runs before the engine starts: checks whether game data is already supplied
 * via CLI arguments, bundled next to the executable (Tarball / Flatpak /
 * Linglong), placed next to the AppImage, or installed under the XDG per-user
 * data directory (${XDG_DATA_HOME:-~/.local/share}/<app-id>/data).
 *
 * When no complete game data is present, opens the project's built-in 1920x1080
 * bootstrap UI (matching iOS / Android / OpenHarmony) to download & verify the
 * release asset packs or import local .zip / data.xp3 files.
 */

#ifndef LINUX_BOOTSTRAP_H
#define LINUX_BOOTSTRAP_H

#ifdef __cplusplus
extern "C" {
#endif

/* Runs the bootstrap check / UI on the main thread before engine init.
 * Returns 1 when game data is ready and the engine should start, or 0 when
 * the user closed the bootstrap window and the process should exit cleanly. */
int krkrsdl2_linux_run_bootstrap(int argc, char **argv);

/* Returns the active external data root (UTF-8, no trailing slash) when the
 * bootstrap flow resolved or installed external data, or NULL when bundled /
 * CLI-specified data should be used by SysInitImpl. */
const char *krkrsdl2_linux_data_root(void);

#ifdef __cplusplus
}
#endif

#endif /* LINUX_BOOTSTRAP_H */
