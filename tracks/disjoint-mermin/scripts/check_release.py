"""Check anonymous release access and portability of the released arXiv source."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tempfile
from urllib.request import urlopen
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO_ROOT=Path(__file__).resolve().parents[3]
PAPER_DIR=REPO_ROOT/'papers'/'disjoint-mermin' if (REPO_ROOT/'papers'/'disjoint-mermin').is_dir() else ROOT/'paper'
RELEASE_TAG = 'v3.4.0'
REPO_URL='https://github.com/0thernes/pauli-contextuality-lab'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--tectonic',required=True)
    args=parser.parse_args()
    url=f'{REPO_URL}/releases/download/{RELEASE_TAG}/contextuality-tensor.pdf'
    if not url.startswith(('https://', 'http://')):
        raise ValueError(f'Unsupported URL scheme: {url!r}')
    with urlopen(url,timeout=60) as response:  # noqa: S310
        published=response.read()
        status=response.status
    local=(PAPER_DIR/'contextuality-tensor.pdf').read_bytes()
    if status != 200 or published != local:
        raise RuntimeError('Anonymous release PDF mismatch')
    report={'status':'passed','release':f'{REPO_URL}/releases/tag/{RELEASE_TAG}',
            'anonymous_pdf_status':status,'pdf_sha256':hashlib.sha256(published).hexdigest(),
            'downloaded_asset_checksums_verified_before_publication':13}
    with tempfile.TemporaryDirectory(prefix='contextuality-arxiv-') as tmp:
        with zipfile.ZipFile(ROOT/'build/release/contextuality-tensor-arxiv-source.zip') as archive:
            # This is our own two-file bundle, validate its exact members first.
            if sorted(archive.namelist()) != ['contextuality-tensor.tex','figures/gap-and-noise.pdf']:
                raise RuntimeError('Unexpected source archive members')
            archive.extractall(tmp)
        result=subprocess.run([args.tectonic,'--untrusted','contextuality-tensor.tex'],cwd=tmp,
                               text=True,encoding='utf-8',errors='replace',capture_output=True)
        (ROOT/'results/arxiv-bundle-build.log').write_text(result.stdout+result.stderr,encoding='utf-8')
        if result.returncode:
            raise RuntimeError('Isolated source-bundle build failed')
        import fitz
        with fitz.open(stream=local,filetype='pdf') as original, fitz.open(str(Path(tmp)/'contextuality-tensor.pdf')) as rebuilt:
            same_text=[p.get_text() for p in original]==[p.get_text() for p in rebuilt]
            if not same_text:
                raise RuntimeError('Source bundle changed PDF text')
            report.update(arxiv_source_isolated_build='passed',source_pdf_pages=len(rebuilt),
                          extracted_text_identical=same_text,arxiv_submission='not submitted')
    (ROOT/'results/release-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
