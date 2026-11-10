// The Click website. Its pages are the human-written guide in `../guide`;
// this directory holds only the site's configuration and theme.
import { readdirSync, readFileSync, utimesSync } from 'node:fs'
import { createRequire } from 'node:module'
import { fileURLToPath } from 'node:url'
import { defineConfig } from 'vitepress'

const guideDir = fileURLToPath(new URL('../../guide', import.meta.url))
const configFile = fileURLToPath(import.meta.url)
const require = createRequire(import.meta.url)

// The sidebar lists every page in `guide/`, so adding a page needs no change
// here. A page's label is its first `# heading`. Pages sort by the `order`
// number in their frontmatter, then by file name; pages without `order` come
// last.
function guidePages() {
  return readdirSync(guideDir)
    .filter((name) => name.endsWith('.md') && name !== 'README.md' && name !== 'index.md')
    .map((name) => {
      const source = readFileSync(`${guideDir}/${name}`, 'utf8')
      const frontmatter = source.match(/^---\n([\s\S]*?)\n---/)?.[1] ?? ''
      const order = Number(frontmatter.match(/^order:\s*(\d+)\s*$/m)?.[1] ?? Infinity)
      const slug = name.slice(0, -'.md'.length)
      const text = source.match(/^#\s+(.+)$/m)?.[1].trim() ?? slug
      return { text, link: `/${slug}`, order, name }
    })
    .sort((a, b) => a.order - b.order || a.name.localeCompare(b.name))
    .map(({ text, link }) => ({ text, link }))
}

// The dev server reads this file once. When a page is added, removed,
// retitled, or reordered, touch this file so the server reloads it and
// rebuilds the sidebar.
function reloadSidebarOnChange() {
  let current = JSON.stringify(guidePages())
  return {
    name: 'click-guide-sidebar',
    configureServer(server) {
      const check = (file: string) => {
        if (!file.startsWith(guideDir) || !file.endsWith('.md')) return
        const next = JSON.stringify(guidePages())
        if (next === current) return
        current = next
        const now = new Date()
        utimesSync(configFile, now, now)
      }
      server.watcher.on('add', check).on('unlink', check).on('change', check)
    },
  }
}

// The URL path the site is served under, with a trailing slash:
// `scripts/build-site.sh` sets it for a deployment.
const base = process.env.CLICK_SITE_BASE ?? '/'

export default defineConfig({
  base,
  srcDir: '../guide',
  // `guide/README.md` is the directory's note on GitHub, not a site page. The
  // home page is `guide/index.md`.
  srcExclude: ['README.md'],
  outDir: '../target/click-site',
  cacheDir: '../target/click-site-cache',

  title: 'Click',
  description: 'A verifier for existing C, C++, and Rust programs.',
  cleanUrls: true,
  // The AI reference is a separate mdBook that the deployment serves under
  // `/reference/`, so a guide link into it has no page here to check.
  ignoreDeadLinks: [/^\/reference\//],

  // The pages are outside this directory, so their compiled imports of Vue
  // can't find `site/node_modules` by walking up from `guide/`. Resolve them
  // here.
  vite: {
    plugins: [reloadSidebarOnChange()],
    resolve: {
      alias: [
        { find: /^vue\/server-renderer$/, replacement: require.resolve('vue/server-renderer') },
        { find: /^vue$/, replacement: require.resolve('vue') },
      ],
    },
  },

  themeConfig: {
    sidebar: [{ text: 'Guide', items: guidePages() }],
    outline: { level: [2, 3] },
    search: { provider: 'local' },
    socialLinks: [{ icon: 'github', link: 'https://github.com/clicklang/click' }],
    // The default theme shows the footer only on a page without a sidebar,
    // such as a home page with `layout: home`.
    footer: {
      message: `AI agents: read the <a href="${base}reference/">reference</a> or <a href="${base}llms.txt">llms.txt</a>.`,
    },
    editLink: {
      pattern: 'https://github.com/clicklang/click/edit/master/guide/:path',
    },
  },
})
