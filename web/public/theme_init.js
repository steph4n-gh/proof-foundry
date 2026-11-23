/* Anti-flash theme initializer (CSP-safe external script; matches app.js pf-theme-v3 key). */
try {
  if (window.localStorage.getItem("pf-theme-v3") === "dark") {
    document.documentElement.setAttribute("data-theme", "dark");
  }
} catch {
  /* private mode */
}
