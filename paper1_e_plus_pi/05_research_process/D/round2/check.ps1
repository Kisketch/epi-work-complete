param($dir)
$env:LEAN_PATH=$dir+';'+$env:LEAN_PATH
& lean (Join-Path $dir Parity.lean)
exit $LASTEXITCODE
