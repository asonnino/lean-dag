-- Promote the leading level-1 heading to document metadata, so pandoc renders
-- a title block instead of a duplicate heading.
function Pandoc(doc)
  for i, blk in ipairs(doc.blocks) do
    if blk.t == "Header" and blk.level == 1 then
      doc.meta.title = pandoc.MetaInlines(blk.content)
      table.remove(doc.blocks, i)
      break
    end
  end
  return doc
end
