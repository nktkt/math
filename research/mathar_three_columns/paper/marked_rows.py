"""Regenerate the vector figure used in the three-column counting note."""

from pathlib import Path

import reportlab
from reportlab.lib.colors import HexColor
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen.canvas import Canvas


MATRICES = (
    ((0, 1, 1), (1, 0, 0), (0, 1, 0)),
    ((1, 1, 1), (1, 0, 0), (0, 1, 0)),
    ((1, 1, 1), (0, 0, 0), (1, 1, 1)),
)


def draw_matrix(canvas, center, rows):
    ink = HexColor("#202830")
    left, right = center - 28, center + 28
    for k, row in enumerate(rows):
        baseline = 55 - 15 * k
        if all(row):
            canvas.setFillColor(HexColor("#D8E4EA"))
            canvas.rect(left + 1, baseline - 3, right - left - 2, 14, fill=1, stroke=0)
        canvas.setFillColor(ink)
        canvas.setFont("VeraBold" if all(row) else "Vera", 13)
        for j, item in enumerate(row):
            canvas.drawCentredString(center + (j - 1) * 17, baseline, str(item))

    canvas.setStrokeColor(ink)
    canvas.setLineWidth(0.9)
    for edge, direction in ((left, 1), (right, -1)):
        path = canvas.beginPath()
        path.moveTo(edge + 4 * direction, 66)
        path.lineTo(edge, 66)
        path.lineTo(edge, 21)
        path.lineTo(edge + 4 * direction, 21)
        canvas.drawPath(path)
    canvas.setFillColor(ink)
    canvas.setFont("Vera", 10)
    canvas.drawCentredString(center, 5, f"q = {sum(all(row) for row in rows)}")


if __name__ == "__main__":
    font_dir = Path(reportlab.__file__).parent / "fonts"
    for name, file in (("Vera", "Vera.ttf"), ("VeraBold", "VeraBd.ttf")):
        pdfmetrics.registerFont(TTFont(name, str(font_dir / file)))
    target = Path(__file__).with_name("marked-rows.pdf")
    canvas = Canvas(str(target), pagesize=(304, 70), invariant=1, pageCompression=1,
                    initialFontName="Vera")
    canvas.setTitle("Full rows in three binary matrices")
    for center, matrix in zip((48, 152, 256), MATRICES):
        draw_matrix(canvas, center, matrix)
    canvas.save()
