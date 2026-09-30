$ErrorActionPreference = 'Stop'
$ProgressPreference = 'SilentlyContinue'
[Net.ServicePointManager]::SecurityProtocol = [Net.ServicePointManager]::SecurityProtocol -bor [Net.SecurityProtocolType]::Tls12

function Stop-ClickInstall([string] $Message) {
    [Console]::Error.WriteLine("click installer: $Message")
    exit 1
}

$repository = if ($env:CLICK_RELEASE_REPOSITORY) { $env:CLICK_RELEASE_REPOSITORY } else { 'clicklang/click' }
if ($repository -notmatch '^[A-Za-z0-9._-]+/[A-Za-z0-9._-]+$') {
    Stop-ClickInstall 'CLICK_RELEASE_REPOSITORY must be owner/name'
}

$version = $env:CLICK_VERSION
if (-not $version -or $version -eq 'latest') {
    try {
        $release = Invoke-RestMethod `
            -Uri "https://api.github.com/repos/$repository/releases/latest" `
            -Headers @{ Accept = 'application/vnd.github+json'; 'User-Agent' = 'clicklang-installer' }
        $version = [string]$release.tag_name
    }
    catch {
        Stop-ClickInstall 'could not look up the latest Click release'
    }
}
$version = $version -replace '^v', ''
if ($version -notmatch '^[A-Za-z0-9][A-Za-z0-9.+-]*$' -or $version.Contains('..') -or $version.EndsWith('.')) {
    Stop-ClickInstall "invalid Click version: $version"
}

if ($env:CLICK_HOME) {
    $clickHome = $env:CLICK_HOME
}
else {
    $clickHome = Join-Path $HOME '.click'
}
$clickHome = [IO.Path]::GetFullPath($clickHome)
$installDirectory = Join-Path $clickHome 'bin'
$installerFile = Join-Path ([IO.Path]::GetTempPath()) "clicklang-installer-$PID-$([Guid]::NewGuid().ToString('N')).ps1"
$installerUrl = "https://github.com/$repository/releases/download/v$version/clicklang-installer.ps1"

Write-Host "Installing Click $version from $repository..."
try {
    Invoke-WebRequest -Uri $installerUrl -OutFile $installerFile -UseBasicParsing
    $oldInstallDirectory = $env:CLICKLANG_INSTALL_DIR
    $oldClickHome = $env:CLICK_HOME
    try {
        $env:CLICKLANG_INSTALL_DIR = $installDirectory
        $global:LASTEXITCODE = 0
        $env:CLICK_HOME = $clickHome
        & $installerFile
        if ($LASTEXITCODE -and $LASTEXITCODE -ne 0) {
            throw "the release installer exited with code $LASTEXITCODE"
        }
    }
    finally {
        $env:CLICKLANG_INSTALL_DIR = $oldInstallDirectory
        $env:CLICK_HOME = $oldClickHome
    }
}
catch {
    Stop-ClickInstall "could not install Click ${version}: $($_.Exception.Message)"
}
finally {
    Remove-Item -LiteralPath $installerFile -Force -ErrorAction SilentlyContinue
}

$launcher = Join-Path $installDirectory 'click.exe'
if (-not (Test-Path -LiteralPath $launcher -PathType Leaf)) {
    Stop-ClickInstall "the release installer did not place click at $launcher"
}
$env:CLICK_HOME = $clickHome
try {
    & $launcher install $version
    if ($LASTEXITCODE -ne 0) { Stop-ClickInstall "could not install Click $version into the version manager" }
    & $launcher default $version
    if ($LASTEXITCODE -ne 0) { Stop-ClickInstall "could not set Click $version as the default" }
}
finally {
    $env:CLICK_HOME = $oldClickHome
}
Write-Host "Click $version is ready. Restart your shell if click is not on PATH yet."
