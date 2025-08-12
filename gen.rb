# Run statemachine.rb and get its stdout
require "open3"
output, status = Open3.capture2e("ruby", "-Ilib", "statemachine.rb")
raise "Error running statemachine.rb: #{output}" unless status.success?
# Open the template lsra.html.in and replace @@CONTENT@@ with the output
File.open("lsra.html.in", "r") do |file|
  content = file.read
  content.gsub!("@@CONTENT@@", output)
  # Write the modified content to lsra.html
  File.open("lsra.html", "w") do |output_file|
    output_file.write(content)
  end
end
