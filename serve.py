import os
from http.server import SimpleHTTPRequestHandler, HTTPServer

BOOK_SITE = os.path.abspath('./book/_site')
DOCS_SITE = os.path.abspath('./analysis/.lake/build/doc')

class CustomHTTPRequestHandler(SimpleHTTPRequestHandler):
    def translate_path(self, path):
        # Serve /analysis-book/docs/* from DOCS_SITE
        if path.startswith('/analysis-book/docs/'):
            rel_path = path[len('/analysis-book/docs/'):]
            return os.path.join(DOCS_SITE, rel_path)
        # Serve /analysis-book/* from BOOK_SITE
        elif path.startswith('/analysis-book/'):
            rel_path = path[len('/analysis-book/'):]
            return os.path.join(BOOK_SITE, rel_path)
        # Otherwise, serve nothing (could return a non-existent path)
        else:
            raise FileNotFoundError("File not found")
    

if __name__ == '__main__':
    PORT = 8000
    handler = CustomHTTPRequestHandler
    with HTTPServer(("", PORT), handler) as httpd:
        print(f"Serving at http://localhost:{PORT}/analysis-book")
        print(f"/analysis-book: {BOOK_SITE}")
        print(f"/analysis-book/docs: {DOCS_SITE}")
        httpd.serve_forever()

